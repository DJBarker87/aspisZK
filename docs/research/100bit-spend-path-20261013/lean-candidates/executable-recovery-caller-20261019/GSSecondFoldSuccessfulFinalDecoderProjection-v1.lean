import GSConcreteRootRecovery
import GSConcreteInterpolation
import GSActualMessageRecoveryFromWitness
import GSFinalMessageCandidateFilter
import SecondFoldSparseProjectionBridge
import SecondFoldSparseProjectionCore
import SecondFoldMatched
import AspisFormal.V7ExactOneFoldDomains
import GSFixedInputDecoderFamily
import GSFixedInputDecoderFamilyLiteralWords
import RRFinalMessageRecovery

set_option autoImplicit false

namespace AspisWide.GSSecondFoldSuccessfulFinalDecoderProjection

open scoped BigOperators

open CompPoly CompPoly.CBivariate
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.Agreement
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisWide.GSActualMessageRecoveryFromWitness
open AspisWide.GSCloseCandidateFiltering
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSFixedInputDecoderBankLiteralWords
open AspisWide.GSFixedInputDecoderFamilyLiteralWords
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.RRFinalMessageRecovery
open AspisR1.GSConcreteRootRecovery
open AspisR1.SecondFoldMatched
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisR1.SecondFoldSparseProjectionCore
open AspisR1.SecondFoldSparseProjectionBridge
open AspisR1.ConcreteProjection

attribute [local irreducible] AspisR1.GSConcreteRootRecovery.initial
  AspisR1.GSConcreteRootRecovery.final
  AspisR1.GSConcreteInterpolation.initial AspisR1.GSConcreteInterpolation.final

variable [Field WideExact] [BEq WideExact] [LawfulBEq WideExact]
  [DecidableEq WideExact] [NeZero (2 : WideExact)]
  [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]
  [Fintype WideExact] [LawfulBEq (CPolynomial WideExact)]

/-- A successful concrete final-decoder result for a literal received word,
combined with the exact final interpolation and encoder bridges, includes any
2390-supported second-fold message in both the filtered list and the sparse
projection. The encoder equalities remain explicit until the WideExact bridge
is consumed. -/
theorem successful_final_decode_includes_sparse
    (received : SmallWord WideExact)
    (points : Array (WideExact × WideExact))
    (hsize : points.size = 262144)
    (hpoints : points = finalLiteralPoints (repeatedWord received))
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (cs : List (List WideExact))
    (hraw : AspisR1.GSConcreteRootRecovery.final q t
      points hsize H.2 = some cs)
    (m : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hmatch : ∀ i ∈ S, secondEncoder m i = received i)
    (hencode : ∀ a : FinalMessage WideExact,
      (encodeFinal a).toPoly = finalConversion.messagePolynomial a)
    (hdegree : ∀ a : FinalMessage WideExact, degreeLt (encodeFinal a) 256) :
    m ∈ projectFinalCandidates
      (GSFinalMessageCandidateFilter.filterCandidates cs) ∧
    AspisR1.sparseLift m ∈
      AspisWide.GSCloseCandidateFiltering.finalCloseOutput
        (repeatedWord received) cs := by
  have hsize' : (finalLiteralPoints (repeatedWord received)).size = 262144 :=
    finalLiteralPoints_size (repeatedWord received)
  have hraw' : AspisR1.GSConcreteRootRecovery.final q t
      (finalLiteralPoints (repeatedWord received)) hsize' H.2 = some cs := by
    simpa [hpoints] using hraw
  obtain ⟨Q, hQrun, hc⟩ := final_correct q t
    (finalLiteralPoints (repeatedWord received)) hsize' hq H.2 cs hraw'
  have hw := AspisR1.GSConcreteInterpolation.final_spec
    (finalLiteralPoints (repeatedWord received)) hsize' Q hQrun
  have hQ : ValidInterpolationWitness (finalNormalizedPoints (repeatedWord received))
      ⟨256, 3, 28673⟩ Q := by
    simpa [finalLiteralPoints_eq_normalized] using hw
  let receivedLane := repeatedWord received
  have hagreement : 9558 ≤ (agreementSet
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact)
        (AspisR1.sparseLift m)) receivedLane).card :=
    sparseLift_final_agreement_of_second_match received m S hS hmatch
  have hclose : closeAtLeast 9558
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
      receivedLane (AspisR1.sparseLift m) := by
    simpa [closeAtLeast, agreementCount,
      AspisV5FriCoherentCandidateExtraction.agreementSet,
      repeatedWord, receivedLane] using hagreement
  have hfinalset : AspisR1.sparseLift m ∈ finalCloseSet receivedLane := by
    simpa [finalCloseSet] using hclose
  have hcloseOutput : AspisR1.sparseLift m ∈
      AspisWide.GSCloseCandidateFiltering.finalCloseOutput receivedLane cs :=
    (finalCloseOutput_eq_finalCloseSet receivedLane (AspisR1.sparseLift m)
      Q cs hQ hc (hencode (AspisR1.sparseLift m))
      (hdegree (AspisR1.sparseLift m))).2 hfinalset
  have hfiltered : AspisR1.sparseLift m ∈
      GSFinalMessageCandidateFilter.filterCandidates cs :=
    final_close_message_mem receivedLane (AspisR1.sparseLift m)
      Q cs hQ hc (hencode (AspisR1.sparseLift m))
      (hdegree (AspisR1.sparseLift m)) hclose
  refine ⟨?_, hcloseOutput⟩
  apply projectFinalCandidates_mem_iff.mpr
  exact ⟨AspisR1.sparseLift m, hfiltered, rfl⟩

/-- Four channel words from `second_match` each survive when the corresponding
literal final-decoder calls succeed. This is the per-lane statement used by a
29-initial/5-final fixed-input bank; it makes no equality assumption between
the four channel words. -/
theorem second_match_all_successful_final_decodes_include_sparse
    (g : Fin 4 → SmallWord WideExact)
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (roots : Fin 4 → List (List WideExact))
    (familyPoints : Fin 5 → Array (WideExact × WideExact))
    (familySizes : ∀ i, (familyPoints i).size = 262144)
    (laneOf : Fin 4 → Fin 5)
    (familyPoints_eq : ∀ s, familyPoints (laneOf s) =
      finalLiteralPoints (repeatedWord (g s)))
    (hraw : ∀ s : Fin 4,
      AspisR1.GSConcreteRootRecovery.final q t
        (familyPoints (laneOf s)) (familySizes (laneOf s)) H.2 = some (roots s))
    (hencode : ∀ a : FinalMessage WideExact,
      (encodeFinal a).toPoly = finalConversion.messagePolynomial a)
    (hdegree : ∀ a : FinalMessage WideExact, degreeLt (encodeFinal a) 256) :
    ∃ b : Fin 4 → SmallMessage WideExact,
      f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
      (∀ s, b s ∈ projectFinalCandidates
        (GSFinalMessageCandidateFilter.filterCandidates (roots s))) ∧
      (∀ s, AspisR1.sparseLift (b s) ∈
        AspisWide.GSCloseCandidateFiltering.finalCloseOutput
          (repeatedWord (g s)) (roots s)) := by
  obtain ⟨b, hb, hf⟩ := AspisR1.SecondFoldMatched.second_match
    g alpha hgood f S hS hvalid
  refine ⟨b, hf, ?_, ?_⟩
  · intro s
    exact (successful_final_decode_includes_sparse
      (g s) (familyPoints (laneOf s)) (familySizes (laneOf s))
      (familyPoints_eq s) q t hq H (roots s) (hraw s) (b s) S hS
      (fun i hi => (hb i hi s).symm) hencode hdegree).1
  · intro s
    exact (successful_final_decode_includes_sparse
      (g s) (familyPoints (laneOf s)) (familySizes (laneOf s))
      (familyPoints_eq s) q t hq H (roots s) (hraw s) (b s) S hS
      (fun i hi => (hb i hi s).symm) hencode hdegree).2


/-- Specialize the four-lane statement to successful final outputs from the
actual 29+5 fixed-input family bank. Lane zero remains V; each second-fold
channel uses its own repeated final word in lanes `Fin.succ s`. -/
theorem second_match_five_lane_bank_success_includes_sparse
    (g : Fin 4 → SmallWord WideExact)
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (inputs : AspisR1.GSFixedInputDecoderFamily.Inputs WideExact 5)
    (V : FinalWord WideExact)
    (roots : Fin 4 → List (List WideExact))
    (hpoints : ∀ i, inputs.finalPoints i =
      finalLiteralPoints (fiveFinalWords V g i))
    (hbank : ∀ s : Fin 4,
      (AspisR1.GSFixedInputDecoderFamily.run q t inputs H).2
        (Fin.succ s) = some (roots s))
    (hencode : ∀ a : FinalMessage WideExact,
      (encodeFinal a).toPoly = finalConversion.messagePolynomial a)
    (hdegree : ∀ a : FinalMessage WideExact, degreeLt (encodeFinal a) 256) :
    ∃ b : Fin 4 → SmallMessage WideExact,
      f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
      (∀ s, b s ∈ projectFinalCandidates
        (GSFinalMessageCandidateFilter.filterCandidates (roots s))) ∧
      (∀ s, AspisR1.sparseLift (b s) ∈
        AspisWide.GSCloseCandidateFiltering.finalCloseOutput
          (repeatedWord (g s)) (roots s)) := by
  have hraw (s : Fin 4) :
      AspisR1.GSConcreteRootRecovery.final q t
        (inputs.finalPoints (Fin.succ s))
        (inputs.finalSize (Fin.succ s)) H.2 = some (roots s) := by
    simpa only [AspisR1.GSFixedInputDecoderFamily.run] using hbank s
  have hpoints' (s : Fin 4) : inputs.finalPoints (Fin.succ s) =
      finalLiteralPoints (repeatedWord (g s)) := by
    simpa [fiveFinalWords, repeatSmallWord] using hpoints (Fin.succ s)
  exact second_match_all_successful_final_decodes_include_sparse
    g alpha hgood f S hS hvalid q t hq H roots
    inputs.finalPoints inputs.finalSize Fin.succ hpoints' hraw hencode hdegree


/-- Fully literal caller specialization: all five final input arrays are
constructed from V and the four repeated channel words, then each successful
family-bank lane yields the exact projected sparse message. -/
theorem second_match_literal_five_lane_bank_success_includes_sparse
    (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact)
    (g : Fin 4 → SmallWord WideExact)
    (alpha : WideExact)
    (hgood : alpha ∉ AspisR1.SecondFoldMatched.secondBad g)
    (f : SmallMessage WideExact)
    (S : Finset (Fin 65536)) (hS : 2390 ≤ S.card)
    (hvalid : ∀ i ∈ S, curveValue g alpha i = secondEncoder f i)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (roots : Fin 4 → List (List WideExact))
    (hbank : ∀ s : Fin 4,
      (AspisR1.GSFixedInputDecoderFamily.run q t
        (AspisWide.GSFixedInputDecoderFamilyLiteralWords.fromReceivedWords W V g) H).2
          (Fin.succ s) = some (roots s))
    (hencode : ∀ a : FinalMessage WideExact,
      (encodeFinal a).toPoly = finalConversion.messagePolynomial a)
    (hdegree : ∀ a : FinalMessage WideExact, degreeLt (encodeFinal a) 256) :
    ∃ b : Fin 4 → SmallMessage WideExact,
      f = ∑ s : Fin 4, alpha ^ s.val • b s ∧
      (∀ s, b s ∈ projectFinalCandidates
        (GSFinalMessageCandidateFilter.filterCandidates (roots s))) ∧
      (∀ s, AspisR1.sparseLift (b s) ∈
        AspisWide.GSCloseCandidateFiltering.finalCloseOutput
          (repeatedWord (g s)) (roots s)) := by
  apply second_match_five_lane_bank_success_includes_sparse
    g alpha hgood f S hS hvalid q t hq H
    (AspisWide.GSFixedInputDecoderFamilyLiteralWords.fromReceivedWords W V g)
    V roots ?_ hbank hencode hdegree
  intro i
  exact AspisWide.GSFixedInputDecoderFamilyLiteralWords.finalPoints_eq W V g i

#print axioms successful_final_decode_includes_sparse
#print axioms second_match_all_successful_final_decodes_include_sparse
#print axioms second_match_five_lane_bank_success_includes_sparse
#print axioms second_match_literal_five_lane_bank_success_includes_sparse

end AspisWide.GSSecondFoldSuccessfulFinalDecoderProjection
