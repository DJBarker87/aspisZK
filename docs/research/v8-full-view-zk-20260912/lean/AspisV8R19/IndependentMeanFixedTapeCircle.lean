import AspisV8R19.IndependentMeanFixedTapeQM31
import AspisV8R19.SamplerObservedCircleProgram
import AspisV8R19.DistinctCircleProgram
import AspisV8R19.CirclePairPrefixProgram

/-! Structural fixed-tape certificates for the bounded circle programs.

Only the query-count certificates are constructed here.  Every error and
retry branch remains in the source `Program`; no distribution, freshness,
source-equivalence, or security statement is made. -/
set_option autoImplicit false
namespace AspisV8R19.IndependentMeanFixedTapeCircle

open DuplexFrames SourceDuplexStep SourceOraclePrograms
open Aeneas Aeneas.Std Result AspisR72Sampler
open MemoizedProgramLaw OracleProgramOps
open AspisV8R19.IndependentMeanFixedTape
open AspisV8R19.IndependentMeanFixedTapeQM31
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.BoundedSamplerWrapper

variable {O E : Type}

abbrev Point := CirclePairPrefixProgram.Point
abbrev CircleError := CirclePairPrefixProgram.CircleError

def challengeCert (hc : ∀ s : State, Within (challengeProgram s) 66)
    (s : State) := hc s

def boundedProgram_within
    (accept : List Nat → Option O) (inner outer : E)
    (hc : ∀ s : State, Within (challengeProgram s) 66) :
    (n : Nat) → (s : State) →
      Within (BoundedSamplerWrapper.program accept inner outer n s) (66 * n)
  | 0, s => Within.done _ 0
  | n + 1, s => by
      have h := withinBind 66 (66 * n) (challengeProgram s)
        (fun r => match r.1 with
          | none => .done (Except.error inner, r.2)
          | some xs => match accept xs with
            | some y => .done (Except.ok y, r.2)
            | none => BoundedSamplerWrapper.program accept inner outer n r.2)
        (hc s)
        (fun r => by
          cases hr : r.1 with
          | none =>
              simp only [hr]
              change Within (.done (Except.error inner, r.2)) (66 * n)
              exact Within.done _ (66 * n)
          | some xs =>
              cases ha : accept xs with
              | some y =>
                  simp only [hr, ha]
                  change Within (.done (Except.ok y, r.2)) (66 * n)
                  exact Within.done _ (66 * n)
              | none =>
                  simp only [hr, ha]
                  change Within (BoundedSamplerWrapper.program accept inner outer n r.2)
                    (66 * n)
                  exact boundedProgram_within accept inner outer hc n r.2)
      change Within (OracleProgramOps.bind (challengeProgram s) (fun r =>
        match r.1 with
        | none => .done (Except.error inner, r.2)
        | some xs => match accept xs with
          | some y => .done (Except.ok y, r.2)
          | none => BoundedSamplerWrapper.program accept inner outer n r.2))
        (66 * (n + 1))
      rw [show 66 * (n + 1) = 66 + 66 * n by omega]
      exact h

def samplerCircle_within (hc : ∀ s : State, Within (challengeProgram s) 66)
    (s : State) :
    Within (SamplerObservedCircleProgram.program s) 198 := by
  exact boundedProgram_within SamplerCirclePolicy.accept
    transcript.CirclePointSampleError.ChallengeSampleExhausted
    transcript.CirclePointSampleError.ParameterSampleExhausted hc 3 s

def distinctCircle_within
    (hc : ∀ s : State, Within (SamplerObservedCircleProgram.program s) 198)
    (first : Point) : (n : Nat) → (s : State) →
      Within (DistinctCircleProgram.program first n s) (198 * n)
  | 0, s => Within.done _ 0
  | n + 1, s => by
      have h := withinBind 198 (198 * n)
        (SamplerObservedCircleProgram.program s)
        (fun r => match r.1 with
          | .error e => .done (Except.error e, r.2)
          | .ok p => if p = first
            then DistinctCircleProgram.program first n r.2
            else .done (Except.ok p, r.2))
        (hc s)
        (fun r => by
          cases hr : r.1 with
          | error e =>
              simp only [hr]
              change Within (.done (Except.error e, r.2)) (198 * n)
              exact Within.done _ (198 * n)
          | ok p =>
              by_cases hp : p = first
              · simp only [hr, hp, if_pos]
                change Within (DistinctCircleProgram.program first n r.2)
                  (198 * n)
                exact distinctCircle_within hc first n r.2
              · simp only [hr, hp, if_neg]
                change Within (.done (Except.ok p, r.2)) (198 * n)
                exact Within.done _ (198 * n))
      change Within (OracleProgramOps.bind (SamplerObservedCircleProgram.program s)
        (fun r => match r.1 with
          | .error e => .done (Except.error e, r.2)
          | .ok p => if p = first
            then DistinctCircleProgram.program first n r.2
            else .done (Except.ok p, r.2)))
        (198 * (n + 1))
      rw [show 198 * (n + 1) = 198 + 198 * n by omega]
      exact h

def absorb_within (s : State) (label : DuplexFrames.Byte) (data : Bytes) :
    Within (absorbProgram s label data) 1 :=
  Within.ask _ _ 0 (fun _ => Within.done _ 0)

def circlePair_within
    (hc : ∀ s : State, Within (challengeProgram s) 66)
    (label : DuplexFrames.Byte) (vector0 vector1 : Bytes) (s : State) :
    Within (CirclePairPrefixProgram.program label vector0 vector1 s) 794 := by
  have hfirst := samplerCircle_within hc s
  have h := withinBind 198 596 (SamplerObservedCircleProgram.program s)
    (fun r => match r.1 with
      | .error e => .done (Except.error e, r.2)
      | .ok first =>
          OracleProgramOps.bind (absorbProgram r.2 label vector0) (fun s1 =>
            OracleProgramOps.bind (DistinctCircleProgram.program first 3 s1)
              (fun r2 => match r2.1 with
                | .error e => .done (Except.error e, r2.2)
                | .ok second => OracleProgramOps.bind
                    (absorbProgram r2.2 label vector1) (fun s2 =>
                      .done (Except.ok (first, second), s2)))))
    (samplerCircle_within hc s)
    (fun r => by
      cases r.1 with
      | error e =>
          change Within (.done (Except.error e, r.2)) 596
          exact Within.done _ 596
      | ok first =>
          have hp := withinBind 1 595 (absorbProgram r.2 label vector0)
            (fun s1 => OracleProgramOps.bind
              (DistinctCircleProgram.program first 3 s1) (fun r2 =>
                match r2.1 with
                | .error e => .done (Except.error e, r2.2)
                | .ok second => OracleProgramOps.bind
                    (absorbProgram r2.2 label vector1) (fun s2 =>
                      .done (Except.ok (first, second), s2))))
            (absorb_within r.2 label vector0)
            (fun s1 => by
              have hd := distinctCircle_within (samplerCircle_within hc) first 3 s1
              have hx : Within
                  (OracleProgramOps.bind (DistinctCircleProgram.program first 3 s1)
                    (fun r2 => match r2.1 with
                      | .error e => .done (Except.error e, r2.2)
                      | .ok second => OracleProgramOps.bind
                          (absorbProgram r2.2 label vector1) (fun s2 =>
                            .done (Except.ok (first, second), s2)))) 595 := by
                rw [show 595 = 594 + 1 by omega]
                exact withinBind 594 1
                  (DistinctCircleProgram.program first 3 s1)
                  (fun r2 => match r2.1 with
                    | .error e => .done (Except.error e, r2.2)
                    | .ok second => OracleProgramOps.bind
                        (absorbProgram r2.2 label vector1) (fun s2 =>
                          .done (Except.ok (first, second), s2)))
                  hd
                  (fun r2 => by
                    cases r2.1 with
                    | error e =>
                        change Within (.done (Except.error e, r2.2)) 1
                        exact Within.done _ 1
                    | ok second =>
                        change Within
                          (OracleProgramOps.bind (absorbProgram r2.2 label vector1)
                            (fun s2 => .done (Except.ok (first, second), s2))) 1
                        rw [show 1 = 1 + 0 by omega]
                        exact withinBind 1 0 (absorbProgram r2.2 label vector1)
                          (fun s2 => .done (Except.ok (first, second), s2))
                          (absorb_within r2.2 label vector1)
                          (fun _ => Within.done _ 0))
              exact hx)
          change Within (OracleProgramOps.bind (absorbProgram r.2 label vector0) _)
            596 at hp
          rw [show 596 = 1 + 595 by omega] at hp
          exact hp)
  change Within (OracleProgramOps.bind (SamplerObservedCircleProgram.program s) _)
    794
  rw [show 794 = 198 + 596 by omega]
  exact h

#print axioms circlePair_within

end AspisV8R19.IndependentMeanFixedTapeCircle
