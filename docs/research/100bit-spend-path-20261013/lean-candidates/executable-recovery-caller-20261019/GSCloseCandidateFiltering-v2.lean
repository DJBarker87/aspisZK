import GSActualMessageRecoveryFromWitness
import InitialResponses

set_option autoImplicit false

namespace AspisWide.GSCloseCandidateFiltering

open CompPoly CompPoly.GuruswamiSudan AspisWideTower
open AspisWide.GSRootCandidateContract
open AspisWide.GSInitialMessageCandidateFilter
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSActualMessageRecoveryFromWitness
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.InitialForwardEncoderBaseV9
open AspisR1.RRFinalMessageRecovery
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder AspisWide.FinalEncoder

variable [Field WideExact] [BEq WideExact] [LawfulBEq WideExact]
  [DecidableEq WideExact] [NeZero (2 : WideExact)]
  [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

/-- Executable finite candidate scan: run the actual public decoder, retain
only messages passing the exact protocol distance check, and deduplicate. -/
def initialCloseOutput (received : InitialWord WideExact)
    (candidates : List (List WideExact)) : Finset (InitialMessage WideExact) :=
  (GSInitialMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (closeAtLeast 38230
      (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact)) received m)) |>.toFinset

theorem initialCloseOutput_eq_Close
    (received : InitialWord WideExact) (m : InitialMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 1025 candidates)
    (hencode : (encodeInitialC m).toPoly = initialConversion.messagePolynomial m)
    (hdegree : degreeLt (encodeInitialC m) 1025) :
    m ∈ initialCloseOutput received candidates ↔ m ∈ AspisR1.InitialResponses.Close received := by
  rw [initialCloseOutput, List.mem_toFinset, List.mem_filter]
  constructor
  · rintro ⟨hfiltered, hdec⟩
    exact (AspisR1.InitialResponses.mem_Close received m).2 (of_decide_eq_true hdec)
  · intro hclose
    have hclose' : closeAtLeast 38230
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact)) received m :=
      (AspisR1.InitialResponses.mem_Close received m).1 hclose
    have hfiltered := initial_close_message_mem received m Q candidates
      hQ hc hencode hdegree hclose'
    exact ⟨hfiltered, decide_eq_true hclose'⟩

/-- Specification-only extensional set for the final distance predicate. The
executable final output below never enumerates this universal set. -/
noncomputable def finalCloseSet (received : FinalWord WideExact) :
    Finset (FinalMessage WideExact) :=
  Finset.univ.filter (fun m => closeAtLeast 9558
    (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact)) received m)

/-- Executable finite candidate scan and deduplication for the final message. -/
def finalCloseOutput (received : FinalWord WideExact)
    (candidates : List (List WideExact)) : Finset (FinalMessage WideExact) :=
  (GSFinalMessageCandidateFilter.filterCandidates candidates).filter
    (fun m => decide (closeAtLeast 9558
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact)) received m)) |>.toFinset

theorem finalCloseOutput_eq_finalCloseSet
    (received : FinalWord WideExact) (m : FinalMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (finalNormalizedPoints received)
      ⟨256, 3, 28673⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 256 candidates)
    (hencode : (encodeFinal m).toPoly = finalConversion.messagePolynomial m)
    (hdegree : degreeLt (encodeFinal m) 256) :
    m ∈ finalCloseOutput received candidates ↔ m ∈ finalCloseSet received := by
  rw [finalCloseOutput, List.mem_toFinset, List.mem_filter,
    finalCloseSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hdec⟩
    exact of_decide_eq_true hdec
  · intro hclose
    have hfiltered := final_close_message_mem received m Q candidates
      hQ hc hencode hdegree hclose
    exact ⟨hfiltered, decide_eq_true hclose⟩

theorem initialCloseOutput_card_le_100
    (received : InitialWord WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 1025 candidates)
    (hencode : ∀ x, (encodeInitialC x).toPoly = initialConversion.messagePolynomial x)
    (hdegree : ∀ x, degreeLt (encodeInitialC x) 1025) :
    (initialCloseOutput received candidates).card ≤ 100 := by
  have hset : initialCloseOutput received candidates = AspisR1.InitialResponses.Close received := by
    ext x
    exact initialCloseOutput_eq_Close received x Q candidates hQ hc
      (hencode x) (hdegree x)
  rw [hset]
  exact AspisR1.InitialResponses.Close_card received

#print axioms initialCloseOutput_eq_Close
#print axioms finalCloseOutput_eq_finalCloseSet
#print axioms initialCloseOutput_card_le_100

end AspisWide.GSCloseCandidateFiltering
