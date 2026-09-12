import SameBodyAuthenticatedSlots
import SelectedPackedQueryBridgeV3

/-! DRAFT pending the parent's focused historical-variant build.
Authenticated same-body records, after the checked ordered inverse constructor,
produce evaluations of the folded quotient of the two prefix-derived words.
No observedWord, polynomiality/image assumption or supplied FixedInput occurs.
The explicit Data/inverse, chronological prefixes/hash law and functional
Merkle-success inputs still require their actual source producers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
namespace AspisV8.SameBodyAuthenticatedFold
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.SelectedWireBytes AspisV8.SelectedWireMerkleRun
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.PackedQueryRecord AspisV8.SameBodyAuthenticatedSlots
open AspisV8.OODInterpolant AspisV8.PostQueryFunctional
noncomputable section

abbrev K := QM31Exact
abbrev Byte := AspisPool.V7MerkleQueryGrammar.Byte
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

-- Transport already proved scalar equalities; do not reduce the giant circle
-- domain or nested tower inverse merely to match the intermediate expression.
attribute [local irreducible] SelectedPackedQueryBridge.recordFold
attribute [local irreducible] QueriedResidual.sourceFold

theorem same_body_authenticated_fold_or_failure
    (view : RawHashInput → Digest208) (body : List Byte)
    (query : Fin 22 → Position) (merkle : SuccessfulMerkleRun view query body)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (MinimalMultiproofPaths.leafLog query (wireRecords merkle.wire) ++ merkle.trace) fullLog)
    (canonical : (parseRecords merkle.wire).isSome = true)
    (d : Data (K := K)) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c
      (SelectedQueryBuffer.points query) = some out) (alpha : K) :
    AuthenticationFailure view c1Prefix c2Prefix (wireRoots merkle.wire) fullLog query ∨
      ∃ decoded : Fin 22 → Decoded,
        parseRecords merkle.wire = some decoded ∧
        (∀ i, merkle.wire.record i = PackedQueryRecord.bodyRecord body i) ∧
        ∀ i : Fin 22,
          SelectedPackedQueryBridge.recordFold d decoded query out alpha i =
            (SelectedReceivedOracle.oracle (0 : Fin 1024 → K)
              (SelectedQuotientOriginal.virtual d
                (prefixBatch c1Prefix c2Prefix merkle.wire d.gamma))).folded alpha
                  (storedPoint (K := K) (query i)) := by
  rcases same_body_authenticated_slots_or_failure view body query merkle
      c1Prefix c2Prefix fullLog c1Answers c2Answers c1Included c2Included
      callsIncluded canonical d.gamma with bad | good
  · exact Or.inl bad
  · obtain ⟨decoded, parsedAll, bodyRecords, slots⟩ := good
    have parsed := parseRecords_success merkle.wire decoded parsedAll
    have checked := (SelectedQueryBuffer.inverse_eq d query).symm.trans inverse
    refine Or.inr ⟨decoded, parsedAll, bodyRecords, ?_⟩
    intro i
    have actualToSource := SelectedPackedQueryBridge.matching_fold d
      (fun j => merkle.wire.record j) decoded parsed query out
      (prefixBatch c1Prefix c2Prefix merkle.wire d.gamma)
      (fun j slot => (slots j slot).2) alpha i
    have sourceToQuotient := QueriedResidual.success_fold d
      (prefixBatch c1Prefix c2Prefix merkle.wire d.gamma) query out checked alpha i
    exact actualToSource.trans sourceToQuotient

#print same_body_authenticated_fold_or_failure
#print axioms same_body_authenticated_fold_or_failure
end
end AspisV8.SameBodyAuthenticatedFold
