import AspisV8R19.DistinctCircleProgram
import AspisV8R19.SourceOraclePrograms

/-! Exact OOD pair prefix for the selected research callback.

The first secure-circle sampler is followed by vector-0 absorption, the
bounded distinct-second wrapper, and vector-1 absorption only after success.
All sampler and outer-exhaustion errors remain visible.  This is an
eval/run correspondence leaf only; it makes no source or distribution claim.
-/
set_option autoImplicit false
namespace AspisV8R19.CirclePairPrefixProgram
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation DuplexFrames SourceDuplexStep SourceOraclePrograms
open SamplerObservedCircleProgram DistinctCircleProgram
open MemoizedProgramLaw OracleProgramOps
open AspisV8R15.ExactTowerBase
noncomputable section

abbrev Point := QM31Exact × QM31Exact
abbrev CircleError := transcript.CirclePointSampleError
abbrev PairResult := Except CircleError (Point × Point) × State

structure PairOut where
  first : Point
  second : Point
  state : State

def program (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes) (s : State) :
    Program Bytes State PairResult :=
  bind (SamplerObservedCircleProgram.program s) (fun r =>
    match r.1 with
    | .error e => .done (.error e, r.2)
    | .ok first =>
        bind (absorbProgram r.2 vectorLabel vector0) (fun s1 =>
          bind (DistinctCircleProgram.program first 3 s1) (fun r2 =>
            match r2.1 with
            | .error e => .done (.error e, r2.2)
            | .ok second =>
                bind (absorbProgram r2.2 vectorLabel vector1) (fun s2 =>
                  .done (.ok (first, second), s2)))))

def absorbRun (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (data : Bytes) (s : State) :
    View Bytes State State :=
  ([(absorb (bytes s) vectorLabel data, H (absorb (bytes s) vectorLabel data))],
    H (absorb (bytes s) vectorLabel data))

def run (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (vector0 vector1 : Bytes)
    (s : State) : View Bytes State PairResult :=
  let r1 := SamplerCircleBridge.modelRun H 3 s
  match r1.2.1 with
  | .error e => (r1.1, (.error e, r1.2.2))
  | .ok first =>
      let r0 := absorbRun H vectorLabel vector0 r1.2.2
      let r2 := DistinctCircleProgram.run H first 3 r0.2
      match r2.2.1 with
      | .error e => (r1.1 ++ r0.1 ++ r2.1, (.error e, r2.2.2))
      | .ok second =>
          let r3 := absorbRun H vectorLabel vector1 r2.2.2
          (r1.1 ++ r0.1 ++ r2.1 ++ r3.1,
            (.ok (first, second), r3.2))

theorem eval_run (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (vector0 vector1 : Bytes) (s : State) :
    eval H (program vectorLabel vector0 vector1 s) =
      run H vectorLabel vector0 vector1 s := by
  have hcircle : eval H (SamplerObservedCircleProgram.program s) =
      SamplerCircleBridge.modelRun H 3 s := by
    unfold SamplerObservedCircleProgram.program SamplerCircleBridge.modelRun
    exact BoundedSamplerWrapper.exact_run
      SamplerCirclePolicy.accept
      transcript.CirclePointSampleError.ChallengeSampleExhausted
      transcript.CirclePointSampleError.ParameterSampleExhausted H 3 s
  simp only [program, eval_bind, hcircle]
  generalize hmodel : SamplerCircleBridge.modelRun H 3 s = r1
  cases r1 with
  | mk trace1 out1 =>
      cases out1 with
      | mk result1 state1 =>
          cases result1 with
          | error e =>
              simp [run, hmodel, MemoizedProgramLaw.eval]
          | ok first =>
              let r0 := absorbRun H vectorLabel vector0 state1
              have habsorb0 : eval H (absorbProgram state1 vectorLabel vector0) = r0 := by
                simpa only [r0, absorbRun] using
                  (SourceOraclePrograms.absorb_eval H state1 vectorLabel vector0)
              rw [eval_bind, habsorb0]
              dsimp only
              have hdistinct := DistinctCircleProgram.eval_run H first 3 r0.2
              rw [eval_bind, hdistinct]
              dsimp only
              generalize hsecond : DistinctCircleProgram.run H first 3 r0.2 = r2
              cases r2 with
              | mk trace2 out2 =>
                  cases out2 with
                  | mk result2 state2 =>
                      cases result2 with
                      | error e =>
                          simp [run, hmodel, hsecond, r0, MemoizedProgramLaw.eval,
                            List.append_assoc]
                      | ok second =>
                          let r3 := absorbRun H vectorLabel vector1 state2
                          have habsorb1 : eval H (absorbProgram state2 vectorLabel vector1) = r3 := by
                            simpa only [r3, absorbRun] using
                              (SourceOraclePrograms.absorb_eval H state2 vectorLabel vector1)
                          simp [eval_bind, run, hmodel, hsecond, habsorb1, r0, r3,
                            MemoizedProgramLaw.eval, List.append_assoc]

#print axioms eval_run
end
end AspisV8R19.CirclePairPrefixProgram
