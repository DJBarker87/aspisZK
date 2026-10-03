import AspisV8R19.SamplerObservedChallenge
import AspisV8R19.SamplerCursorTightBound

set_option autoImplicit false
namespace AspisV8R19.R464ObservedChallengeTraceBound

open AspisV8R19.SamplerObservedChallenge
open AspisV8R19.SamplerCursorTightBound
open AspisV8R19.SamplerObservation
open AspisV8R19.QM31SamplerProgram
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep
open AspisV8R19.DuplexFrames
open AspisV8R19.SamplerChallengeBridge (encodeResult)
open Aeneas Aeneas.Std AspisR72Sampler

abbrev State := SourceDuplexStep.State
abbrev Bytes := DuplexFrames.Bytes
abbrev Trace := SamplerObservation.Trace

/-- The instrumented trace is exactly the prior decoded trace followed by
the source run's calls. -/
theorem challenge_observed_trace_length_eq (H : Bytes → State) (s : State)
    (history : Trace) :
    ∃ observed,
      SamplerObservedSource.challenge_qm31 (transcriptFor H s) history =
        .ok ((encodeResult (challengeRun H s).2.1,
          transcriptFor H (challengeRun H s).2.2), observed) ∧
      (decodeTrace observed).length =
        (decodeTrace history).length + (challengeRun H s).1.length := by
  obtain ⟨observed, hchallenge, htrace⟩ := challenge_trace H s history
  refine ⟨observed, hchallenge, ?_⟩
  rw [htrace, List.length_append]

theorem challenge_observed_trace_bound (H : Bytes → State) (s : State)
    (history : Trace) :
    ∃ observed,
      SamplerObservedSource.challenge_qm31 (transcriptFor H s) history =
        .ok ((encodeResult (challengeRun H s).2.1,
          transcriptFor H (challengeRun H s).2.2), observed) ∧
      (decodeTrace observed).length ≤ (decodeTrace history).length + 8 := by
  obtain ⟨observed, hchallenge, hlength⟩ :=
    challenge_observed_trace_length_eq H s history
  refine ⟨observed, hchallenge, ?_⟩
  rw [hlength]
  exact Nat.add_le_add_left (challengeRun_trace_bound H s) _

#print axioms challenge_observed_trace_length_eq
#print axioms challenge_observed_trace_bound

end AspisV8R19.R464ObservedChallengeTraceBound
