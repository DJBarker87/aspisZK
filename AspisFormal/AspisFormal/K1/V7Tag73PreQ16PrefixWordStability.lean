import AspisFormal.K1.V7Tag73K13PreQ16TargetProbability
import AspisFormal.Pool.V7MerklePrefixTargetCongruence

/-!
# Prefix-word stability outside the causal Merkle-target event

Appending one fresh root record cannot change a Merkle path which was already
resolved by the earlier chronological prefix.  If it resolves a previously
missing root or child, its answer necessarily hits the conservative candidate
inventory already exposed by that prefix.  This file makes that deterministic
step explicit before iterating it over an arbitrary suffix.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73PreQ16PrefixWordStability

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73K13PreQ16TargetInventory
open AspisK1.V7Tag73K13PreQ16TargetProbability
open AspisK1.V7Tag73K13PreQ16TargetSchedulerTree
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.V7MerklePartialPathExtractor
open AspisPool.V7MerkleFirstUnresolvedBinding
open AspisPool.V7MerklePrefixTargetCongruence
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleQueryGrammar

noncomputable section

/-- Appending chronological records can only enlarge the conservative
208-bit Merkle candidate inventory. -/
theorem prefixMerkleCandidateSet_exposure_append_left
    (records later : List UnifiedExposureRecord) :
    prefixMerkleCandidateSet (exposurePrefixRawQueries records) ⊆
      prefixMerkleCandidateSet
        (exposurePrefixRawQueries (records ++ later)) := by
  intro digest digestMem
  unfold prefixMerkleCandidateSet at digestMem ⊢
  obtain ⟨rawInput, rawInputMem, candidateMem⟩ :=
    Finset.mem_biUnion.mp digestMem
  apply Finset.mem_biUnion.mpr
  refine ⟨rawInput, ?_, candidateMem⟩
  rw [List.mem_toFinset] at rawInputMem ⊢
  simpa [exposurePrefixRawQueries, List.filterMap_append,
    List.map_append] using Or.inl rawInputMem

/-- Appending records preserves every first lookup already present in the
prefix. -/
theorem exposurePrefixLookup_append_of_some
    (prior suffix : List UnifiedExposureRecord) (input : ShaInput)
    (answer : Digest256)
    (found : exposurePrefixLookup prior input = some answer) :
    exposurePrefixLookup (prior ++ suffix) input = some answer := by
  induction prior with
  | nil => simp [exposurePrefixLookup] at found
  | cons head tail ih =>
      simp only [List.cons_append, exposurePrefixLookup] at found ⊢
      by_cases same : causalInput? head = some input
      · simpa [same] using found
      · simp only [same, ↓reduceIte] at found ⊢
        exact ih found

/-- The prefix-local and extended truncation views agree on every raw input
which was already advertised by the prefix. -/
theorem exposurePrefixTruncate_append_agrees_on_prefix
    (prior suffix : List UnifiedExposureRecord) (rawInput : RawHashInput)
    (member : rawInput ∈ exposurePrefixRawQueries prior) :
    exposurePrefixTruncate (prior ++ suffix) rawInput =
      exposurePrefixTruncate prior rawInput := by
  obtain ⟨digest, found⟩ :=
    exposurePrefixRawQueries_member_has_lookup prior rawInput member
  have extended := exposurePrefixLookup_append_of_some prior suffix
    (rawHashInputToRuntimeInput rawInput) digest found
  simp [exposurePrefixTruncate, found, extended]

/-- A successful chronological lookup advertises the corresponding raw input
in the same prefix log. -/
theorem exposurePrefixLookup_some_implies_raw_member
    (records : List UnifiedExposureRecord) (input : ShaInput)
    (answer : Digest256)
    (found : exposurePrefixLookup records input = some answer) :
    runtimeInputToRawHashInput input ∈ exposurePrefixRawQueries records := by
  induction records with
  | nil => simp [exposurePrefixLookup] at found
  | cons head tail ih =>
      simp only [exposurePrefixLookup] at found
      by_cases same : causalInput? head = some input
      · simp only [same, ↓reduceIte, Option.some.injEq] at found
        unfold exposurePrefixRawQueries
        simp [same]
      · simp only [same, ↓reduceIte] at found
        have tailMember := ih found
        unfold exposurePrefixRawQueries at tailMember ⊢
        cases headInput : causalInput? head <;>
          simp [headInput, tailMember]

/-- If the input was absent from the prefix, appending its first causal record
installs exactly that record's answer. -/
theorem exposurePrefixLookup_append_single_of_none
    (records : List UnifiedExposureRecord) (record : UnifiedExposureRecord)
    (input : ShaInput)
    (missing : exposurePrefixLookup records input = none)
    (recordInput : causalInput? record = some input) :
    exposurePrefixLookup (records ++ [record]) input = some record.answer := by
  induction records with
  | nil => simp [exposurePrefixLookup, recordInput]
  | cons head tail ih =>
      simp only [List.cons_append, exposurePrefixLookup] at missing ⊢
      by_cases same : causalInput? head = some input
      · simp [same] at missing
      · simp only [same, ↓reduceIte] at missing ⊢
        exact ih missing

/-- Membership in the lifted 256-bit target inventory is exactly membership
of the deployed 208-bit prefix. -/
theorem answer_not_target_prefix
    (records : List UnifiedExposureRecord) (answer : Digest256)
    (target : AspisPool.V7MerkleQueryGrammar.Digest208)
    (targetMem : target ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (answerMiss : answer ∉ preQ16FullMerkleTargets records) :
    runtimeDigest256PrefixToMerkleDigest answer ≠ target := by
  intro prefixExact
  apply answerMiss
  unfold preQ16FullMerkleTargets deployedPrefixTargetPreimage
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, by simpa [prefixExact] using targetMem⟩

theorem resolveInput_append_of_some
    (truncateSha256 : RawHashInput →
      AspisPool.V7MerkleQueryGrammar.Digest208)
    (target : AspisPool.V7MerkleQueryGrammar.Digest208)
    (prior suffix : OrderedRawQueryLog) (input : RawHashInput)
    (found : resolveInput truncateSha256 target prior = some input) :
    resolveInput truncateSha256 target (prior ++ suffix) = some input := by
  unfold resolveInput at found ⊢
  rw [List.find?_append, found]
  rfl

/-- A single later record whose answer misses the current causal target
inventory cannot change resolution of any root or child already named by that
inventory. -/
theorem resolveInput_append_single_eq_of_answer_miss
    (records : List UnifiedExposureRecord) (record : UnifiedExposureRecord)
    (target : AspisPool.V7MerkleQueryGrammar.Digest208)
    (targetMem : target ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (answerMiss : record.answer ∉ preQ16FullMerkleTargets records) :
    resolveInput (exposurePrefixTruncate (records ++ [record])) target
        (exposurePrefixRawQueries (records ++ [record])) =
      resolveInput (exposurePrefixTruncate records) target
        (exposurePrefixRawQueries records) := by
  let priorLog := exposurePrefixRawQueries records
  let priorView := exposurePrefixTruncate records
  let extendedView := exposurePrefixTruncate (records ++ [record])
  have agree : ∀ input ∈ priorLog,
      extendedView input = priorView input := by
    intro input member
    exact exposurePrefixTruncate_append_agrees_on_prefix records [record]
      input member
  have priorResolution := resolveInput_eq_of_agree_on_log extendedView
    priorView priorLog agree target
  cases priorExact : resolveInput priorView target priorLog with
  | some input =>
      have extendedPrior : resolveInput extendedView target priorLog =
          some input := by
        rw [priorResolution]
        exact priorExact
      have extendedFull := resolveInput_append_of_some extendedView target
        priorLog (exposurePrefixRawQueries [record]) input extendedPrior
      simpa [priorLog, extendedView, exposurePrefixRawQueries,
        List.filterMap_append, List.map_append] using extendedFull
  | none =>
      have extendedPrior : resolveInput extendedView target priorLog = none := by
        rw [priorResolution]
        exact priorExact
      cases causalExact : causalInput? record with
      | none =>
          simpa [priorLog, priorView, extendedView, exposurePrefixRawQueries,
            List.filterMap_append, causalExact] using extendedPrior
      | some runtimeInput =>
          let rawInput := runtimeInputToRawHashInput runtimeInput
          have rawMiss : extendedView rawInput ≠ target := by
            cases oldLookup : exposurePrefixLookup records runtimeInput with
            | some digest =>
                have rawMember : rawInput ∈ priorLog := by
                  exact exposurePrefixLookup_some_implies_raw_member records
                    runtimeInput digest oldLookup
                have priorMiss := resolveInput_none_excludes_matching_member
                  priorView target priorLog priorExact rawInput rawMember
                exact fun equal => priorMiss ((agree rawInput rawMember).symm.trans
                  equal)
            | none =>
                have installed := exposurePrefixLookup_append_single_of_none
                  records record runtimeInput oldLookup causalExact
                have valueExact : extendedView rawInput =
                    runtimeDigest256PrefixToMerkleDigest record.answer := by
                  simp [extendedView, rawInput, exposurePrefixTruncate,
                    runtimeInputToRawHashInput_roundtrip, installed]
                exact fun equal =>
                  answer_not_target_prefix records record.answer target targetMem
                    answerMiss (valueExact.symm.trans equal)
          have logExact : exposurePrefixRawQueries (records ++ [record]) =
              priorLog ++ [rawInput] := by
            simp [priorLog, rawInput, exposurePrefixRawQueries,
              List.filterMap_append, causalExact]
          rw [logExact]
          unfold resolveInput at extendedPrior ⊢
          rw [List.find?_append, extendedPrior]
          simpa [extendedView] using rawMiss

/-- Every node child exposed by one raw input in the prefix belongs to the
conservative candidate inventory used by the causal target tree. -/
theorem parsed_node_children_mem_prefix_candidates
    (prior : List UnifiedExposureRecord) (input : RawHashInput)
    (member : input ∈ exposurePrefixRawQueries prior)
    (left right : AspisPool.V7MerkleQueryGrammar.Digest208)
    (parsed : parseTypedPreimage input = some (.node left right)) :
    left ∈ prefixMerkleCandidateSet (exposurePrefixRawQueries prior) ∧
      right ∈ prefixMerkleCandidateSet (exposurePrefixRawQueries prior) := by
  have serialized : input = serialize (.node left right) :=
    (parseTypedPreimage_success_reserializes input (.node left right)
      parsed).symm
  constructor
  · apply rawInput_candidate_mem_prefixMerkleCandidateSet _ input member
    rw [serialized]
    exact node_left_mem_rawInputMerkleCandidates left right
  · apply rawInput_candidate_mem_prefixMerkleCandidateSet _ input member
    rw [serialized]
    exact node_right_mem_rawInputMerkleCandidates left right

/-- The one-record resolver fact lifts through every level of the binary path.
The child digests are already in the prefix candidate inventory because they
occur literally in the resolved parent preimage. -/
theorem resolvePath_append_single_eq_of_answer_miss
    {Leaf : Type} (parseLeaf : RawHashInput → Option Leaf)
    (records : List UnifiedExposureRecord) (record : UnifiedExposureRecord)
    (answerMiss : record.answer ∉ preQ16FullMerkleTargets records) :
    ∀ (height : Nat)
      (target : AspisPool.V7MerkleQueryGrammar.Digest208)
      (position : Nat),
      target ∈ prefixMerkleCandidateSet (exposurePrefixRawQueries records) →
      resolvePath parseLeaf (exposurePrefixTruncate (records ++ [record]))
          (exposurePrefixRawQueries (records ++ [record])) height target
          position =
        resolvePath parseLeaf (exposurePrefixTruncate records)
          (exposurePrefixRawQueries records) height target position := by
  intro height
  induction height with
  | zero =>
      intro target position targetMem
      simp only [resolvePath]
      rw [resolveInput_append_single_eq_of_answer_miss records record target
        targetMem answerMiss]
  | succ height ih =>
      intro target position targetMem
      simp only [resolvePath]
      rw [resolveInput_append_single_eq_of_answer_miss records record target
        targetMem answerMiss]
      cases resolved : resolveInput (exposurePrefixTruncate records) target
          (exposurePrefixRawQueries records) with
      | none => rfl
      | some input =>
          cases parsed : parseTypedPreimage input with
          | none => simp [resolved, parsed]
          | some typed =>
              cases typed with
              | c1Leaf value salt => simp [resolved, parsed]
              | c2Leaf value salt => simp [resolved, parsed]
              | node left right =>
                  have inputMem := resolveInput_success_mem
                    (exposurePrefixTruncate records) target
                    (exposurePrefixRawQueries records) input resolved
                  have children := parsed_node_children_mem_prefix_candidates
                    records input inputMem left right parsed
                  cases direction : position.testBit height <;>
                    simp [parsed, direction, ih, children]

/-- Once both public roots are already exposed by the prefix, one further
record whose answer misses the causal target inventory cannot change the
canonical completed word. -/
theorem preQ16PrefixWords_append_single_eq_of_answer_miss
    (records : List UnifiedExposureRecord) (record : UnifiedExposureRecord)
    (roots : Roots)
    (c1RootMem : roots.c1 ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (c2RootMem : roots.c2 ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (answerMiss : record.answer ∉ preQ16FullMerkleTargets records) :
    preQ16PrefixWords (records ++ [record]) roots =
      preQ16PrefixWords records roots := by
  have c1 :
      (fun position : Position =>
        prefixC1LeafAt
          (exposurePrefixTruncate (records ++ [record]))
          (exposurePrefixRawQueries (records ++ [record])) roots.c1 position) =
        (fun position : Position =>
          prefixC1LeafAt (exposurePrefixTruncate records)
            (exposurePrefixRawQueries records) roots.c1 position) := by
    funext position
    unfold prefixC1LeafAt resolveC1Path
    rw [resolvePath_append_single_eq_of_answer_miss parseC1Leaf records record
      answerMiss treeDepth roots.c1 position.val c1RootMem]
  have c2 :
      (fun position : Position =>
        prefixC2LeafAt
          (exposurePrefixTruncate (records ++ [record]))
          (exposurePrefixRawQueries (records ++ [record])) roots.c2 position) =
        (fun position : Position =>
          prefixC2LeafAt (exposurePrefixTruncate records)
            (exposurePrefixRawQueries records) roots.c2 position) := by
    funext position
    unfold prefixC2LeafAt resolveC2Path
    rw [resolvePath_append_single_eq_of_answer_miss parseC2Leaf records record
      answerMiss treeDepth roots.c2 position.val c2RootMem]
  unfold preQ16PrefixWords extractPrefixFixedWords
  exact congrArg₂ ExtractedWords.mk (congrArg List.ofFn c1)
    (congrArg List.ofFn c2)

/-- Outside the canonical global target event, an arbitrary chronological
suffix of the exact root run cannot change a word whose two public roots were
already exposed at the starting prefix. -/
theorem exact_preQ16PrefixWords_append_eq_of_no_target
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (records suffix : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = records ++ suffix)
    (roots : Roots)
    (c1RootMem : roots.c1 ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (c2RootMem : roots.c2 ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records))
    (noTarget : sample ∉
      exactK13PreQ16MerkleTargetHitEvent configuration transitionFuel) :
    preQ16PrefixWords (records ++ suffix) roots =
      preQ16PrefixWords records roots := by
  induction suffix generalizing records with
  | nil => simp
  | cons record suffix ih =>
      have rootExact' : exactFixedRootRecords input.package.root =
          records ++ record :: suffix := by
        simpa using rootExact
      have answerMiss :
          record.answer ∉ preQ16FullMerkleTargets records :=
        exact_no_merkle_target_excludes_root_later_target input records suffix
          record rootExact' noTarget
      have c1RootMem' : roots.c1 ∈
          prefixMerkleCandidateSet
            (exposurePrefixRawQueries (records ++ [record])) :=
        prefixMerkleCandidateSet_exposure_append_left records [record]
          c1RootMem
      have c2RootMem' : roots.c2 ∈
          prefixMerkleCandidateSet
            (exposurePrefixRawQueries (records ++ [record])) :=
        prefixMerkleCandidateSet_exposure_append_left records [record]
          c2RootMem
      have tailExact : exactFixedRootRecords input.package.root =
          (records ++ [record]) ++ suffix := by
        simpa [List.append_assoc] using rootExact'
      calc
        preQ16PrefixWords (records ++ record :: suffix) roots =
            preQ16PrefixWords ((records ++ [record]) ++ suffix) roots := by
              simp [List.append_assoc]
        _ = preQ16PrefixWords (records ++ [record]) roots :=
          ih (records := records ++ [record]) tailExact c1RootMem'
            c2RootMem'
        _ = preQ16PrefixWords records roots :=
          preQ16PrefixWords_append_single_eq_of_answer_miss records record roots
            c1RootMem c2RootMem answerMiss

#print axioms exposurePrefixLookup_append_of_some
#print axioms exposurePrefixTruncate_append_agrees_on_prefix
#print axioms exposurePrefixLookup_some_implies_raw_member
#print axioms exposurePrefixLookup_append_single_of_none
#print axioms answer_not_target_prefix
#print axioms resolveInput_append_of_some
#print axioms resolveInput_append_single_eq_of_answer_miss
#print axioms resolvePath_append_single_eq_of_answer_miss
#print axioms parsed_node_children_mem_prefix_candidates
#print axioms preQ16PrefixWords_append_single_eq_of_answer_miss
#print axioms exact_preQ16PrefixWords_append_eq_of_no_target

end

end AspisK1.V7Tag73PreQ16PrefixWordStability
