import AuthenticatedEarlyC1Prefix

/-!
Source-review draft. C2 is constructed from its own post-lambda/chi answer
prefix and root, using the same V7 partial-path completion as C1. The cutoff
must precede OOD/gamma in the intended source execution; it is not the early
C1 cutoff, a total oracle supplied after queries, or a source-timing theorem.

One accepted supplied C2 path gives its literal prefix-word projection OR
a later input hashing to the prefix-selected unresolved C2 target OR the
shared raw208-bit collision event. All source-path/trace premises remain
explicit. No probability, full-source acceptance, complete extraction, or
global canonicality claim is made. No q16 wrapper is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.AuthenticatedPhaseWords
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.EarlyC1LateProjection
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor AspisPool.V7MerklePrefixTargetCongruence
open AspisPool.V7MerkleFirstUnresolvedBinding AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleAcceptedOpeningProjection AspisPool.V7MerkleParserRoundtrip
open AspisPool.V7ExtractedLaneWords

/-- Literal C2 decode-or-zero word from the second-phase prefix. Supplying
the real prefix/root at this cutoff is a source execution obligation. -/
def fixedC2 (records : AnswerPrefix) (root : Digest208) : C2Received :=
  c2Received (prefixWords records root)

/-- The resulting field word depends only on the recorded answers, even
when the later oracle view is extended outside the prefix. -/
theorem fixedC2_eq_actual_view
    (records : AnswerPrefix) (root : Digest208)
    (view : RawHashInput → Digest208)
    (answers : ∀ record ∈ records, view record.1 = record.2) :
    fixedC2 records root =
      c2Received (extractPrefixFixedWords view (rawPrefix records) ⟨root, root⟩) := by
  unfold fixedC2
  rw [prefixWords_eq_actual_view records root view answers]

/-- The target is selected by the second-phase prefix resolver. The later
opening position may be adaptive; no negligible probability is attached. -/
def C2OpeningLateTargetHit (view : RawHashInput → Digest208)
    (records : AnswerPrefix) (root : Digest208) (opening : PairedOpening) : Prop :=
  ∃ target,
    firstUnresolvedC2Target (frozenView records) (rawPrefix records) root
      opening.position = some target ∧
    ∃ input ∈ openingInputTrace view opening.position
      (.c2Leaf opening.c2Value opening.sharedSalt) opening.c2Siblings,
      input ∉ rawPrefix records ∧ view input = target

/-- Per-opening C2 counterpart of the already-green C1 alternative. The
shared collision event is unchanged; failure to resolve is not discarded.
The good case fixes the whole packed leaf AND its salt, before decoding. -/
theorem accepted_c2_opening_prefix_or_late_target_or_collision
    (records : AnswerPrefix) (root : Digest208)
    (view : RawHashInput → Digest208) (fullLog : OrderedRawQueryLog)
    (opening : PairedOpening)
    (answers : ∀ record ∈ records, view record.1 = record.2)
    (included : TraceIncludedInLog (rawPrefix records) fullLog)
    (accepted : foldPath view opening.position
      (c2DisclosedLeafDigest view opening) opening.c2Siblings = root)
    (covered : TraceIncludedInLog (openingInputTrace view opening.position
      (.c2Leaf opening.c2Value opening.sharedSalt) opening.c2Siblings) fullLog) :
    (prefixWords records root).c2[opening.position.val]? =
        some ⟨opening.c2Value, opening.sharedSalt⟩ ∨
      C2OpeningLateTargetHit view records root opening ∨
      RawLogTruncatedDigestCollision view fullLog := by
  cases resolved : resolveC2Path view (rawPrefix records) root opening.position with
  | some path =>
      obtain ⟨leaf, siblings, leafAt, authenticates, trace⟩ :=
        resolvedC2Path_yields_covered_prefix_opening view (rawPrefix records)
          root opening.position path resolved
      have canonical : C2CoveredCanonicalOpening view
          (extractPrefixFixedWords view (rawPrefix records) ⟨root, root⟩).c2
          root opening.position fullLog :=
        ⟨leaf, siblings, leafAt, authenticates,
          trace_inclusion_trans _ _ _ trace included⟩
      rcases c2_covered_opening_is_projection_or_raw_collision view _ root opening
          fullLog canonical accepted covered with projection | collision
      · apply Or.inl
        rw [prefixWords_eq_actual_view records root view answers]
        exact projection
      · exact Or.inr (Or.inr collision)
  | none =>
      have targetSome := (resolveC2Path_none_iff_firstUnresolvedC2Target_isSome
        view (rawPrefix records) root opening.position).mp resolved
      obtain ⟨target, targetExact⟩ := Option.isSome_iff_exists.mp targetSome
      let leaf : C2Leaf := ⟨opening.c2Value, opening.sharedSalt⟩
      let leafInput := serialize (.c2Leaf leaf.value leaf.salt)
      have parsed : parseC2Leaf leafInput = some leaf := by
        simp [parseC2Leaf, leafInput, parse_serialize_typed_preimage]
      obtain ⟨path, pathInputs⟩ := authenticatingPath_of_bottomUpOpening
        parseC2Leaf view opening.position.val leafInput leaf parsed
        (List.ofFn opening.c2Siblings)
      have pathCovered : TraceIncludedInLog path.inputs fullLog := by
        intro input member
        rw [pathInputs, List.mem_reverse] at member
        exact covered input member
      have firstTarget : firstUnresolvedTarget parseC2Leaf view (rawPrefix records)
          (List.ofFn opening.c2Siblings).length
          (foldPathAux view opening.position.val (view leafInput)
            (List.ofFn opening.c2Siblings)) opening.position.val = some target := by
        have rootExact : foldPathAux view opening.position.val (view leafInput)
            (List.ofFn opening.c2Siblings) = root := accepted
        rw [List.length_ofFn, rootExact]
        exact targetExact
      rcases firstUnresolvedTarget_yields_later_hit_or_collision parseC2Leaf view
          (rawPrefix records) fullLog included path pathCovered target firstTarget with
        hit | collision
      · obtain ⟨input, member, fresh, digest⟩ := hit
        apply Or.inr (Or.inl ?_)
        refine ⟨target, ?_, input, ?_, fresh, digest⟩
        · change firstUnresolvedTarget parseC2Leaf (frozenView records)
            (rawPrefix records) treeDepth root opening.position.val = some target
          rw [firstUnresolvedTarget_eq_of_agree_on_log parseC2Leaf
            (frozenView records) view (rawPrefix records)
            (frozenView_agrees_on_prefix records view answers)]
          exact targetExact
        · rw [pathInputs, List.mem_reverse] at member
          exact member
      · exact Or.inr (Or.inr collision)

#print axioms fixedC2_eq_actual_view
#print axioms accepted_c2_opening_prefix_or_late_target_or_collision
end AspisV8.AuthenticatedPhaseWords
