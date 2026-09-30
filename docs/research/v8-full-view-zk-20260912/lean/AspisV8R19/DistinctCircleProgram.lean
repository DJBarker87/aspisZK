import AspisV8R19.SamplerObservedCircleProgram

/-! Exact bounded outer retry for the second secure-circle point.

The first point is an explicit input, so the acceptance test is literally
`p ≠ first`.  Inner sampler errors are returned immediately; exhaustion of the
outer distinctness budget is returned as `ParameterSampleExhausted`.  No law
about the distribution of accepted points is asserted here. -/
set_option autoImplicit false
namespace AspisV8R19.DistinctCircleProgram
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open SamplerObservedCircleProgram
open MemoizedProgramLaw OracleProgramOps
open AspisV8R15.ExactTowerBase
noncomputable section

abbrev Point := QM31Exact × QM31Exact
abbrev CircleError := transcript.CirclePointSampleError
abbrev CircleResult := Except CircleError Point × State

def program (first : Point) : Nat → State → Program Bytes State CircleResult
  | 0, s => .done (.error .ParameterSampleExhausted, s)
  | n + 1, s =>
      bind (SamplerObservedCircleProgram.program s) (fun r =>
        match r.1 with
        | .error e => .done (.error e, r.2)
        | .ok p =>
            if p = first then program first n r.2
            else .done (.ok p, r.2))

def run (H : Bytes → State) (first : Point) :
    Nat → State → View Bytes State CircleResult
  | 0, s => ([], (.error .ParameterSampleExhausted, s))
  | n + 1, s =>
      let r := SamplerCircleBridge.modelRun H 3 s
      match r.2.1 with
      | .error e => (r.1, (.error e, r.2.2))
      | .ok p =>
          if p = first then
            let tail := run H first n r.2.2
            (r.1 ++ tail.1, tail.2)
          else (r.1, r.2)

theorem eval_run (H : Bytes → State) (first : Point) (n : Nat) (s : State) :
    eval H (program first n s) = run H first n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have hbase : eval H (SamplerObservedCircleProgram.program s) =
          SamplerCircleBridge.modelRun H 3 s := by
        unfold SamplerObservedCircleProgram.program SamplerCircleBridge.modelRun
        exact BoundedSamplerWrapper.exact_run
          SamplerCirclePolicy.accept
          transcript.CirclePointSampleError.ChallengeSampleExhausted
          transcript.CirclePointSampleError.ParameterSampleExhausted H 3 s
      simp only [program, eval_bind, hbase, run]
      cases hr : SamplerCircleBridge.modelRun H 3 s with
      | mk trace result =>
          rcases result with ⟨out, next⟩
          cases out with
          | error e => simp [MemoizedProgramLaw.eval]
          | ok p =>
              by_cases hp : p = first
              · simp [hp, ih]
              · simp [hp, MemoizedProgramLaw.eval]

#print axioms eval_run
end
end AspisV8R19.DistinctCircleProgram
