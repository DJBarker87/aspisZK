import SelectedMultiproofPrefixProjection
import PrefixPackedQueryBatch
import FixedWordQueryTerminal

/-! Complete typed q22 opening composition.  One selected minimal-multiproof
execution either produces all literal fixed-word opening equalities consumed
by the relation terminal, or exposes a shared collision / phase-specific late
target.  The packed record is the same object on both authentication and field
decoding paths.

This is not yet the refinement from the Rust byte-loop's boolean result to
`MinimalMultiproofPaths.Accepted`.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 300
set_option maxHeartbeats 300000

namespace AspisV8.SelectedMultiproofOpeningEquality
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedMultiproofPrefixProjection
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
open AspisV8.PackedQueryRecord AspisV8.PrefixPackedQueryBatch
open AspisV8.FixedWordQueryTerminal
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

def recordOfBytes (record : List Byte) : Record where
  c1 := c1Bytes record
  c2 := c2Bytes record
  salt := saltBytes record

def AuthenticationFailure (view : RawHashInput → Digest208)
    (c1Prefix c2Prefix : AnswerPrefix) (roots : Digests)
    (fullLog : OrderedRawQueryLog) (query : Fin 22 → Position) : Prop :=
  RawLogTruncatedDigestCollision view fullLog ∨
    C1LateTargetHit view c1Prefix (roots 0) fullLog query ∨
    C2LateTargetHit view c2Prefix (roots 1) fullLog query

/-- Typed selected opening verification establishes exactly the fixed-word
premise used by `FixedWordQueryTerminal`; no root is treated as a total word. -/
theorem accepted_opening_equality_or_authentication_failure
    (view : RawHashInput → Digest208) (roots : Digests)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (queries : OrderedQueryGame.Schedule AspisV8.SelectedReceivedOracle.domain 22)
    (rawRecords : Fin 22 → List Byte) (decoded : Fin 22 → Decoded)
    (frontier : List Digests) (nodeLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog
      (leafLog (indices queries) (fun i => recordOfBytes (rawRecords i)) ++ nodeLog) fullLog)
    (parsed : ∀ i, parse (rawRecords i) = some (decoded i))
    (accepted : Accepted view roots (indices queries)
      (fun i => recordOfBytes (rawRecords i)) frontier nodeLog)
    (fixed : FixedInput)
    (word : fixed.word = AspisV8.NearGammaSelectedC1.rawBatch
      (AspisPool.V7ExtractedLaneWords.c1Received (prefixWords c1Prefix (roots 0)))
      (AspisPool.V7ExtractedLaneWords.c2Received (prefixWords c2Prefix (roots 1)))
      fixed.chord.gamma) :
    AuthenticationFailure view c1Prefix c2Prefix roots fullLog (indices queries) ∨
      OpeningEquality fixed queries rawRecords := by
  rcases accepted_all_projections_or_shared_failure view roots c1Prefix c2Prefix
      fullLog (indices queries) (fun i => recordOfBytes (rawRecords i)) frontier
      nodeLog c1Answers c2Answers c1Included c2Included callsIncluded accepted with
    collision | late1 | late2 | projections
  · exact Or.inl (Or.inl collision)
  · exact Or.inl (Or.inr (Or.inl late1))
  · exact Or.inl (Or.inr (Or.inr late2))
  · apply Or.inr
    intro i slot
    rw [word]
    apply raw_slots_of_paired_projection
      (prefixWords c1Prefix (roots 0)) (prefixWords c2Prefix (roots 1))
      (indices queries i) (rawRecords i) (decoded i) (parsed i)
    exact projections i

#print axioms accepted_opening_equality_or_authentication_failure
end
end AspisV8.SelectedMultiproofOpeningEquality
