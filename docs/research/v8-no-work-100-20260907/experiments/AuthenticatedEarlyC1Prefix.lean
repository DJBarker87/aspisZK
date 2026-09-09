import AspisFormal.Pool.V7MerklePrefixTargetCongruence
import AspisFormal.Pool.V7MerkleFirstUnresolvedBinding
import EarlyC1LateProjection

/-! Prefix-answer-local C1 totalization and one-opening authentication.
No assumption that a root alone supplies a word, no q16 wrapper, and no
probability assigned to the explicit unresolved-target/collision alternatives. -/
set_option autoImplicit false
set_option maxRecDepth 100
set_option maxHeartbeats 200000
namespace AspisV8.AuthenticatedEarlyC1Prefix
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor AspisPool.V7MerklePrefixTargetCongruence
open AspisPool.V7MerkleFirstUnresolvedBinding AspisPool.V7MerkleOpeningBinding
open AspisPool.V7MerkleAcceptedOpeningProjection AspisPool.V7MerkleParserRoundtrip
open AspisPool.V7ExtractedLaneWords AspisV8.EarlyC1Projection

abbrev AnswerPrefix := List (RawHashInput × Digest208)

def answerLookup : AnswerPrefix → RawHashInput → Option Digest208
  | [], _ => none
  | (input, answer) :: rest, target =>
      if input = target then some answer else answerLookup rest target

def rawPrefix (records : AnswerPrefix) : OrderedRawQueryLog := records.map Prod.fst

def frozenView (records : AnswerPrefix) (input : RawHashInput) : Digest208 :=
  (answerLookup records input).getD (fun _ => 0)

def prefixWords (records : AnswerPrefix) (root : Digest208) : ExtractedWords :=
  extractPrefixFixedWords (frozenView records) (rawPrefix records) ⟨root, root⟩

def fixedC1 (records : AnswerPrefix) (root : Digest208) : C1Received :=
  c1Received (prefixWords records root)

noncomputable def fixedEarlyC1 (records : AnswerPrefix) (root : Digest208) :=
  earlyC1 (fixedC1 records root)

theorem lookup_agrees_on_advertised_input
    (records : AnswerPrefix) (view : RawHashInput → Digest208)
    (answers : ∀ record ∈ records, view record.1 = record.2)
    (input : RawHashInput) (member : input ∈ rawPrefix records) :
    answerLookup records input = some (view input) := by
  induction records with
  | nil => simp [rawPrefix] at member
  | cons record rest ih =>
      rcases record with ⟨head, answer⟩
      have headAnswer := answers (head, answer) (by simp)
      have restAnswers : ∀ record ∈ rest, view record.1 = record.2 := by
        intro record present
        exact answers record (by simp [present])
      by_cases same : head = input
      · subst input
        simp [answerLookup, headAnswer]
      · have tailMember : input ∈ rawPrefix rest := by
          change input ∈ head :: rawPrefix rest at member
          exact (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [answerLookup, same] using ih restAnswers tailMember

theorem frozenView_agrees_on_prefix
    (records : AnswerPrefix) (view : RawHashInput → Digest208)
    (answers : ∀ record ∈ records, view record.1 = record.2) :
    ∀ input ∈ rawPrefix records, frozenView records input = view input := by
  intro input member
  simp only [frozenView, lookup_agrees_on_advertised_input records view answers
    input member, Option.getD_some]

theorem prefixWords_eq_actual_view
    (records : AnswerPrefix) (root : Digest208)
    (view : RawHashInput → Digest208)
    (answers : ∀ record ∈ records, view record.1 = record.2) :
    prefixWords records root =
      extractPrefixFixedWords view (rawPrefix records) ⟨root, root⟩ :=
  extractPrefixFixedWords_eq_of_agree_on_log (frozenView records) view
    (rawPrefix records) (frozenView_agrees_on_prefix records view answers) ⟨root, root⟩

/-- A target is chosen by the EARLY resolver; a supplied authenticated path
contains a later input hashing to it. This is not automatically a negligible
event: the causal random-oracle experiment must charge it. -/
def OpeningLateTargetHit (view : RawHashInput → Digest208)
    (records : AnswerPrefix) (root : Digest208) (opening : PairedOpening) : Prop :=
  ∃ target,
    firstUnresolvedC1Target (frozenView records) (rawPrefix records) root
      opening.position = some target ∧
    ∃ input ∈ openingInputTrace view opening.position
      (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings,
      input ∉ rawPrefix records ∧ view input = target

theorem accepted_opening_prefix_or_late_target_or_collision
    (records : AnswerPrefix) (root : Digest208)
    (view : RawHashInput → Digest208) (fullLog : OrderedRawQueryLog)
    (opening : PairedOpening)
    (answers : ∀ record ∈ records, view record.1 = record.2)
    (included : TraceIncludedInLog (rawPrefix records) fullLog)
    (accepted : foldPath view opening.position
      (c1DisclosedLeafDigest view opening) opening.c1Siblings = root)
    (covered : TraceIncludedInLog (openingInputTrace view opening.position
      (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings) fullLog) :
    (prefixWords records root).c1[opening.position.val]? =
        some ⟨opening.c1Value, opening.sharedSalt⟩ ∨
      OpeningLateTargetHit view records root opening ∨
      RawLogTruncatedDigestCollision view fullLog := by
  cases resolved : resolveC1Path view (rawPrefix records) root opening.position with
  | some path =>
      obtain ⟨leaf, siblings, leafAt, authenticates, trace⟩ :=
        resolvedC1Path_yields_covered_prefix_opening view (rawPrefix records)
          root opening.position path resolved
      have canonical : C1CoveredCanonicalOpening view
          (extractPrefixFixedWords view (rawPrefix records) ⟨root, root⟩).c1
          root opening.position fullLog :=
        ⟨leaf, siblings, leafAt, authenticates,
          trace_inclusion_trans _ _ _ trace included⟩
      rcases c1_covered_opening_is_projection_or_raw_collision view _ root opening
          fullLog canonical accepted covered with projection | collision
      · apply Or.inl
        rw [prefixWords_eq_actual_view records root view answers]
        exact projection
      · exact Or.inr (Or.inr collision)
  | none =>
      have targetSome := (resolveC1Path_none_iff_firstUnresolvedC1Target_isSome
        view (rawPrefix records) root opening.position).mp resolved
      obtain ⟨target, targetExact⟩ := Option.isSome_iff_exists.mp targetSome
      let leaf : C1Leaf := ⟨opening.c1Value, opening.sharedSalt⟩
      let leafInput := serialize (.c1Leaf leaf.value leaf.salt)
      have parsed : parseC1Leaf leafInput = some leaf := by
        simp [parseC1Leaf, leafInput, parse_serialize_typed_preimage]
      obtain ⟨path, pathInputs⟩ := authenticatingPath_of_bottomUpOpening
        parseC1Leaf view opening.position.val leafInput leaf parsed
        (List.ofFn opening.c1Siblings)
      have pathCovered : TraceIncludedInLog path.inputs fullLog := by
        intro input member
        rw [pathInputs, List.mem_reverse] at member
        exact covered input member
      have firstTarget : firstUnresolvedTarget parseC1Leaf view (rawPrefix records)
          (List.ofFn opening.c1Siblings).length
          (foldPathAux view opening.position.val (view leafInput)
            (List.ofFn opening.c1Siblings)) opening.position.val = some target := by
        have rootExact : foldPathAux view opening.position.val (view leafInput)
            (List.ofFn opening.c1Siblings) = root := accepted
        rw [List.length_ofFn, rootExact]
        exact targetExact
      rcases firstUnresolvedTarget_yields_later_hit_or_collision parseC1Leaf view
          (rawPrefix records) fullLog included path pathCovered target firstTarget with
        hit | collision
      · obtain ⟨input, member, fresh, digest⟩ := hit
        apply Or.inr (Or.inl ?_)
        refine ⟨target, ?_, input, ?_, fresh, digest⟩
        · change firstUnresolvedTarget parseC1Leaf (frozenView records)
            (rawPrefix records) treeDepth root opening.position.val = some target
          rw [firstUnresolvedTarget_eq_of_agree_on_log parseC1Leaf
            (frozenView records) view (rawPrefix records)
            (frozenView_agrees_on_prefix records view answers)]
          exact targetExact
        · rw [pathInputs, List.mem_reverse] at member
          exact member
      · exact Or.inr (Or.inr collision)

#print axioms lookup_agrees_on_advertised_input
#print axioms frozenView_agrees_on_prefix
#print axioms prefixWords_eq_actual_view
#print axioms accepted_opening_prefix_or_late_target_or_collision
end AspisV8.AuthenticatedEarlyC1Prefix
