import AspisV8R19.CirclePairHistoryLaw
import AspisV8R19.IndependentAnswerTransport

/-! Raw-word reparameterisation of the cached-oracle pair-prefix law.

The only premise is the same explicit `FreshFrom` premise as the history law.
The complete error/result/state view and supplied prior history are retained.
-/
set_option autoImplicit false
namespace AspisV8R19.CirclePairRawIndependentLaw

open Aeneas Aeneas.Std Result AspisR72Sampler
open DuplexFrames SourceDuplexStep
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
open AdaptiveFirstReadLaw
open CirclePairPrefixProgram CirclePairHistoryLaw
open IndependentAnswerTransport
open SamplerRawStateRepresentation
open SamplerObservation SqueezeOracleBridge

theorem cached_oracle_history_eq_raw_independentMean
    (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes)
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (fresh : FreshFrom (program vectorLabel vector0 vector1 s) t)
    (test : Result (View Bytes State CirclePairPrefixProgram.PairResult) → ℚ) :
    mean (fun H :
      {i // i ∈ support (program vectorLabel vector0 vector1 s)} → State =>
      test (observe
        (complete t (extend (support (program vectorLabel vector0 vector1 s)) H fallback))
        vectorLabel vector0 vector1 s history)) =
      independentMean
        (recodeAnswers stateRawEquiv (program vectorLabel vector0 vector1 s))
        ((fun view => test (.ok (decodeTrace history ++ view.1, view.2))) ∘
          decodeView stateRawEquiv) := by
  rw [CirclePairHistoryLaw.cached_oracle_history_eq_independentMean
    vectorLabel vector0 vector1 s history t fallback fresh test]
  exact (independentMean_stateRaw_transport
    (program vectorLabel vector0 vector1 s)
    (fun view => test (.ok (decodeTrace history ++ view.1, view.2)))).symm

#print axioms cached_oracle_history_eq_raw_independentMean
end AspisV8R19.CirclePairRawIndependentLaw
