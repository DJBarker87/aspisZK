import V7CallerCurrentReleaseR30SecureCircleCanonical

/-!
# Canonical literal circle tensor factors for the current production caller

This focused module follows the generated `add_circle_tensor` source from a
canonical sampled point through each doubling, push, and final reversal.  It
keeps the loop proof separate so it can reuse the checked secure-circle sampler
without replaying it.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30CircleFactorsCanonical

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30SecureCircleCanonical
open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR26AcceptedTailTrace

abbrev RawQM31 := field.QM31
abbrev RawWeights := sumcheck.WeightAccumulator

/-- Elementwise canonicality for vectors built by the current circle source.
This is definitionally the tensor semantic interface used by the terminal
bridge, but is kept local here to avoid replaying that large dependency. -/
def CanonicalFactors (values : List RawQM31) : Prop :=
  ∀ value ∈ values, GeneratedCanonicalQM31 value

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

private theorem qm31_one_canonical :
    GeneratedCanonicalQM31 field.QM31.ONE := by
  unfold GeneratedCanonicalQM31 GeneratedCanonicalCM31
  simp only [field.QM31.ONE]
  repeat' constructor <;>
    norm_num [AspisAeneasCM31Multiplicative.CanonicalRawM31]

/-- Canonicality is closed under appending one generated field element. -/
private theorem canonical_append
    (values : List RawQM31) (value : RawQM31)
    (valuesCanonical : CanonicalFactors values)
    (valueCanonical : GeneratedCanonicalQM31 value) :
    CanonicalFactors (values ++ [value]) := by
  intro present member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact valuesCanonical present member
  · exact valueCanonical

/-- Reversing the literal vector does not affect its element canonicality. -/
private theorem canonical_reverse
    (values : List RawQM31) (canonical : CanonicalFactors values) :
    CanonicalFactors values.reverse := by
  intro value member
  exact canonical value (by simpa using member)

private theorem push_exact {T : Type}
    (values valuesOut : alloc.vec.Vec T) (value : T)
    (run : alloc.vec.Vec.push values value = ok valuesOut) :
    valuesOut.val = values.val ++ [value] := by
  unfold alloc.vec.Vec.push at run
  simp only at run
  split at run
  · simpa [List.concat_eq_append] using
      congrArg Subtype.val (Result.ok.inj run).symm
  · cases run

/-- The generated `circle.double_x` helper retains canonical limbs. -/
private theorem successful_double_x_canonical
    (x output : RawQM31) (xCanonical : GeneratedCanonicalQM31 x)
    (run : circle.double_x x = ok output) :
    GeneratedCanonicalQM31 output := by
  unfold circle.double_x at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨square, squareRun, run⟩ := run
  obtain ⟨expectedSquare, expectedSquareRun, squareCanonical, _⟩ :=
    generated_qm31_square_corresponds x xCanonical
  have squareExact : square = expectedSquare :=
    Result.ok.inj (squareRun.symm.trans expectedSquareRun)
  rw [squareExact] at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨doubled, doubledRun, run⟩ := run
  obtain ⟨expectedDoubled, expectedDoubledRun, doubledCanonical, _⟩ :=
    generated_qm31_add_corresponds expectedSquare expectedSquare
      squareCanonical squareCanonical
  have doubledExact : doubled = expectedDoubled :=
    Result.ok.inj (doubledRun.symm.trans expectedDoubledRun)
  rw [doubledExact] at run
  obtain ⟨expectedOutput, expectedOutputRun, outputCanonical, _⟩ :=
    generated_qm31_sub_corresponds expectedDoubled field.QM31.ONE
      doubledCanonical qm31_one_canonical
  have outputExact : output = expectedOutput :=
    Result.ok.inj (run.symm.trans expectedOutputRun)
  rw [outputExact]
  exact outputCanonical

/-- One literal body state of the generated circle-factor loop. -/
private abbrev CircleFactorState :=
  core.ops.range.Range Std.U32 × alloc.vec.Vec RawQM31 × RawQM31

private def circle_factor_body (state : CircleFactorState) :
    Result (ControlFlow CircleFactorState (alloc.vec.Vec RawQM31)) :=
  sumcheck.WeightAccumulator.impl.add_circle_tensor_loop.body state.1 state.2.1
    state.2.2

/-- A continuing source edge appends a canonical doubled coordinate and uses
that coordinate as the next recurrence input. -/
private theorem circle_factor_body_cont_canonical
    (state next : CircleFactorState)
    (edge : circle_factor_body state = ok (cont next))
    (factorsCanonical : CanonicalFactors state.2.1.val)
    (xCanonical : GeneratedCanonicalQM31 state.2.2) :
    CanonicalFactors next.2.1.val ∧ GeneratedCanonicalQM31 next.2.2 := by
  rcases state with ⟨iter, factors, x⟩
  rcases next with ⟨iterNext, factorsNext, xNext⟩
  change CanonicalFactors factors.val at factorsCanonical
  change GeneratedCanonicalQM31 x at xCanonical
  change CanonicalFactors factorsNext.val ∧ GeneratedCanonicalQM31 xNext
  unfold circle_factor_body at edge
  unfold sumcheck.WeightAccumulator.impl.add_circle_tensor_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iteratorNext⟩
  cases option with
  | none =>
      simp only at edge
      cases edge
  | some index =>
      rw [bind_eq_ok_iff] at edge
      obtain ⟨doubled, doubledRun, edge⟩ := edge
      have doubledCanonical := successful_double_x_canonical x doubled
        xCanonical doubledRun
      rw [bind_eq_ok_iff] at edge
      obtain ⟨factorsOut, pushRun, edge⟩ := edge
      have factorsExact : factorsOut.val = factors.val ++ [doubled] :=
        push_exact factors factorsOut doubled pushRun
      have stateExact : (iterNext, factorsNext, xNext) =
          (iteratorNext, factorsOut, doubled) :=
        (ControlFlow.cont.inj (Result.ok.inj edge)).symm
      have factorsNextExact : factorsNext = factorsOut := by
        exact congrArg (fun pair : CircleFactorState => pair.2.1) stateExact
      have xNextExact : xNext = doubled := by
        exact congrArg (fun pair : CircleFactorState => pair.2.2) stateExact
      rw [factorsNextExact, xNextExact, factorsExact]
      exact ⟨canonical_append factors.val doubled factorsCanonical
        doubledCanonical, doubledCanonical⟩

/-- A terminating source edge returns the accumulated factor vector. -/
private theorem circle_factor_body_done_canonical
    (state : CircleFactorState) (output : alloc.vec.Vec RawQM31)
    (edge : circle_factor_body state = ok (done output))
    (factorsCanonical : CanonicalFactors state.2.1.val) :
    CanonicalFactors output.val := by
  rcases state with ⟨iter, factors, x⟩
  change CanonicalFactors factors.val at factorsCanonical
  unfold circle_factor_body at edge
  unfold sumcheck.WeightAccumulator.impl.add_circle_tensor_loop.body at edge
  simp only at edge
  rw [bind_eq_ok_iff] at edge
  obtain ⟨iteratorPair, iteratorRun, edge⟩ := edge
  rcases iteratorPair with ⟨option, iteratorNext⟩
  cases option with
  | none =>
      simp only [Result.ok.injEq, ControlFlow.done.injEq] at edge
      subst output
      exact factorsCanonical
  | some index =>
      rw [bind_eq_ok_iff] at edge
      obtain ⟨doubled, doubledRun, edge⟩ := edge
      rw [bind_eq_ok_iff] at edge
      obtain ⟨factorsOut, pushRun, edge⟩ := edge
      cases edge

private theorem circle_factor_trace_canonical
    {state : CircleFactorState} {output : alloc.vec.Vec RawQM31}
    (trace : ExactLoopTrace circle_factor_body state output)
    (factorsCanonical : CanonicalFactors state.2.1.val)
    (xCanonical : GeneratedCanonicalQM31 state.2.2) :
    CanonicalFactors output.val := by
  induction trace with
  | @done state output edge =>
      exact circle_factor_body_done_canonical state output edge factorsCanonical
  | cont edge tail inductionHypothesis =>
      obtain ⟨nextFactorsCanonical, nextXCanonical⟩ :=
        circle_factor_body_cont_canonical _ _ edge factorsCanonical xCanonical
      exact inductionHypothesis nextFactorsCanonical nextXCanonical

/-- The literal source circle-factor loop retains canonicality for every
factor accumulated before the final reversal. -/
private theorem circle_factor_loop_success_canonical
    (iter : core.ops.range.Range Std.U32)
    (factors output : alloc.vec.Vec RawQM31) (x : RawQM31)
    (factorsCanonical : CanonicalFactors factors.val)
    (xCanonical : GeneratedCanonicalQM31 x)
    (success : sumcheck.WeightAccumulator.impl.add_circle_tensor_loop
      iter factors x = ok output) :
    CanonicalFactors output.val := by
  unfold sumcheck.WeightAccumulator.impl.add_circle_tensor_loop at success
  obtain ⟨trace⟩ := loop_success_yields_exact_trace circle_factor_body
    (iter, factors, x) output success
  exact circle_factor_trace_canonical trace factorsCanonical xCanonical

private def reversed_factors (values : alloc.vec.Vec RawQM31) :
    alloc.vec.Vec RawQM31 :=
  ⟨values.val.reverse, by simpa using values.property⟩

/-- A successful current-production circle append gives the common tensor
inserter a canonical, reversed vector of literal circle factors. -/
theorem successful_circle_append_factors_canonical
    (weights weightsAfter : RawWeights) (scale : RawQM31)
    (point : circle.SecureCirclePoint)
    (xCanonical : GeneratedCanonicalQM31 point.x)
    (yCanonical : GeneratedCanonicalQM31 point.y)
    (success : sumcheck.WeightAccumulator.impl.add_circle_tensor
      weights scale point = ok (.Ok (), weightsAfter)) :
    ∃ factors : alloc.vec.Vec RawQM31,
      sumcheck.WeightAccumulator.impl.add_tensor_factors
          weights scale factors = ok (.Ok (), weightsAfter) ∧
      CanonicalFactors factors.val := by
  unfold sumcheck.WeightAccumulator.impl.add_circle_tensor at success
  by_cases short : weights.log_len < 2#u32
  · rw [if_pos short] at success
    simp at success
  · rw [if_neg short] at success
    simp only [Aeneas.Std.lift, bind_tc_ok] at success
    let empty := alloc.vec.Vec.with_capacity RawQM31
      (UScalar.cast .Usize weights.log_len)
    generalize firstPush : alloc.vec.Vec.push empty point.y = firstResult
      at success
    cases firstResult with
    | fail error => simp at success
    | div => simp at success
    | ok first =>
        simp only [bind_tc_ok] at success
        have firstValues := push_exact empty first point.y firstPush
        have firstCanonical : CanonicalFactors first.val := by
          rw [firstValues]
          exact canonical_append [] point.y (by simp [CanonicalFactors])
            yCanonical
        generalize secondPush : alloc.vec.Vec.push first point.x = secondResult
          at success
        cases secondResult with
        | fail error => simp at success
        | div => simp at success
        | ok second =>
            simp only [bind_tc_ok] at success
            have secondValues := push_exact first second point.x secondPush
            have secondCanonical : CanonicalFactors second.val := by
              rw [secondValues]
              exact canonical_append first.val point.x firstCanonical
                xCanonical
            generalize loopEquation :
                sumcheck.WeightAccumulator.impl.add_circle_tensor_loop
                  { start := 2#u32, «end» := weights.log_len } second
                  point.x = loopResult at success
            cases loopResult with
            | fail error => simp at success
            | div => simp at success
            | ok loopFactors =>
                simp only [bind_tc_ok] at success
                have loopCanonical := circle_factor_loop_success_canonical
                  { start := 2#u32, «end» := weights.log_len } second
                  loopFactors point.x secondCanonical xCanonical loopEquation
                let finalFactors := reversed_factors loopFactors
                have finalCanonical : CanonicalFactors finalFactors.val := by
                  simpa [finalFactors, reversed_factors] using
                    canonical_reverse loopFactors.val loopCanonical
                refine ⟨finalFactors, ?_, finalCanonical⟩
                simpa [empty, finalFactors, reversed_factors,
                  alloc.vec.Vec.deref_mut, core.slice.Slice.reverse] using
                  success

/-- The accepted current circle edge records the same canonical factors that
its source append operation passed to the common tensor inserter. -/
theorem AcceptedCircleStep.factors_canonical
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext) :
    CanonicalFactors step.factors.val := by
  obtain ⟨xCanonical, yCanonical⟩ :=
    successful_challenge_secure_circle_point_canonical state.2.1
      step.transcriptAfterPoint step.point step.pointRun
  obtain ⟨factors, factorsRun, factorsCanonical⟩ :=
    successful_circle_append_factors_canonical state.2.2.2.2
      step.weightsAfter step.scale step.point xCanonical yCanonical
      step.appendRun
  obtain ⟨_, candidateComponents⟩ :=
    successful_tensor_append_exact state.2.2.2.2 step.weightsAfter
      step.scale factors factorsRun
  have trailing :
      [sumcheck.WeightComponent.Tensor step.scale factors] =
        [sumcheck.WeightComponent.Tensor step.scale step.factors] :=
    List.append_cancel_left
      (candidateComponents.symm.trans step.componentsExact)
  have componentExact : sumcheck.WeightComponent.Tensor step.scale factors =
      sumcheck.WeightComponent.Tensor step.scale step.factors :=
    by injection trailing
  injection componentExact with _ factorsExact
  simpa only [factorsExact] using factorsCanonical

#print axioms successful_circle_append_factors_canonical
#print axioms AcceptedCircleStep.factors_canonical

end V7CallerCurrentReleaseR30CircleFactorsCanonical
