import SelectedMultiproofOpeningEquality

/-! Composition of complete typed q22 authentication with the concrete
opened-value terminal. The successful branch is the exact causal relation
acceptance consumed by the selected ideal execution; the other branch is the
single explicitly named authentication failure union.

The remaining source-refinement seam is Rust byte-loop success implying the
typed `MinimalMultiproofPaths.Accepted` and parser/terminal premises below.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 300
set_option maxHeartbeats 300000

namespace AspisV8.SelectedWireOpeningTerminal
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedMultiproofPrefixProjection
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisV8.PackedQueryRecord AspisV8.FixedWordQueryTerminal
open AspisV8.SelectedMultiproofOpeningEquality
open AspisV8.TypedRelationTerminal AspisV8.CausalOrderedRelation
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev M31 := AspisV5ComponentCQM31TowerExact.M31Exact

theorem accepted_terminal_or_authentication_failure
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
    (multiproof : Accepted view roots (indices queries)
      (fun i => recordOfBytes (rawRecords i)) frontier nodeLog)
    (fixed : FixedInput)
    (word : fixed.word = AspisV8.NearGammaSelectedC1.rawBatch
      (AspisPool.V7ExtractedLaneWords.c1Received (prefixWords c1Prefix (roots 0)))
      (AspisPool.V7ExtractedLaneWords.c2Received (prefixWords c2Prefix (roots 1)))
      fixed.chord.gamma)
    (fields : Fields AspisV8.SelectedReceivedOracle.domain 22)
    (tau alpha rho a1 a2 a3 : K)
    (out : List K × List M31)
    (inverse : AspisV8.LineNormBuffer.inverseLines fixed.chord.a fixed.chord.b fixed.chord.c
      (AspisV8.SelectedQueryBuffer.points (indices queries)) = some out)
    (terminal : acceptsValues (fixed.before.snapshot tau (fields.firstResponse tau) alpha)
      (fields.final tau alpha) (fun j => (queries j : K))
      (openedValues fixed decoded queries out alpha) rho
      (fields.later tau alpha queries rho) a1 a2 a3) :
    AuthenticationFailure view c1Prefix c2Prefix roots fullLog (indices queries) ∨
      CausalOrderedRelation.accepts fixed.before fixed.oracle fields.strategy
        tau alpha queries rho [a1,a2,a3] := by
  rcases accepted_opening_equality_or_authentication_failure view roots c1Prefix
      c2Prefix fullLog queries rawRecords decoded frontier nodeLog c1Answers c2Answers
      c1Included c2Included callsIncluded parsed multiproof fixed word with bad | opening
  · exact Or.inl bad
  · exact Or.inr ((acceptance_fixed fixed fields tau alpha queries rho a1 a2 a3
      rawRecords decoded parsed opening out inverse).mp terminal)

#print axioms accepted_terminal_or_authentication_failure
end
end AspisV8.SelectedWireOpeningTerminal
