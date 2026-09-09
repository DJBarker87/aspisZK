import AuthenticatedEarlyC1Prefix

/-! All possible C1 first-unresolved targets are fixed by the early records
and root. A later choice of opening position cannot enlarge this set.
Only deterministic event reduction/cardinality is proved here; the actual
shared-oracle probability and replay accounting remain separate. -/
set_option autoImplicit false
set_option maxRecDepth 100
set_option maxHeartbeats 100000
namespace AspisV8.AuthenticatedEarlyC1Targets
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor AspisPool.V7MerkleOpeningBinding

def targetList (records : AnswerPrefix) (root : Digest208) : List Digest208 :=
  (List.ofFn (fun position : Position =>
    firstUnresolvedC1Target (frozenView records) (rawPrefix records) root position)).filterMap id

noncomputable def allTargets (records : AnswerPrefix) (root : Digest208) : Finset Digest208 := by
  classical
  exact (targetList records root).toFinset

theorem allTargets_card_le (records : AnswerPrefix) (root : Digest208) :
    (allTargets records root).card ≤ 262144 := by
  classical
  calc
    (allTargets records root).card ≤ (targetList records root).length :=
      List.toFinset_card_le (targetList records root)
    _ ≤ (List.ofFn (fun position : Position =>
        firstUnresolvedC1Target (frozenView records) (rawPrefix records) root position)).length :=
      List.length_filterMap_le _ _
    _ = 2 ^ treeDepth := List.length_ofFn
    _ = 262144 := rfl

theorem first_target_mem (records : AnswerPrefix) (root : Digest208)
    (position : Position) (target : Digest208)
    (selected : firstUnresolvedC1Target (frozenView records) (rawPrefix records)
      root position = some target) : target ∈ allTargets records root := by
  classical
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  exact ⟨some target, List.mem_ofFn.mpr ⟨position, selected⟩, rfl⟩

def WholeDomainLaterHit (view : RawHashInput → Digest208)
    (records : AnswerPrefix) (root : Digest208) (fullLog : OrderedRawQueryLog) : Prop :=
  ∃ input ∈ fullLog, input ∉ rawPrefix records ∧ view input ∈ allTargets records root

theorem opening_late_hit_yields_whole_domain_hit
    (view : RawHashInput → Digest208) (records : AnswerPrefix)
    (root : Digest208) (fullLog : OrderedRawQueryLog) (opening : PairedOpening)
    (covered : TraceIncludedInLog (openingInputTrace view opening.position
      (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings) fullLog)
    (hit : OpeningLateTargetHit view records root opening) :
    WholeDomainLaterHit view records root fullLog := by
  obtain ⟨target, selected, input, member, fresh, digest⟩ := hit
  refine ⟨input, covered input member, fresh, ?_⟩
  rw [digest]
  exact first_target_mem records root opening.position target selected

theorem accepted_opening_prefix_or_shared_failure
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
      WholeDomainLaterHit view records root fullLog ∨
      RawLogTruncatedDigestCollision view fullLog := by
  rcases accepted_opening_prefix_or_late_target_or_collision records root view
      fullLog opening answers included accepted covered with projection | hit | collision
  · exact Or.inl projection
  · exact Or.inr (Or.inl (opening_late_hit_yields_whole_domain_hit view records
      root fullLog opening covered hit))
  · exact Or.inr (Or.inr collision)

#print axioms allTargets_card_le
#print axioms first_target_mem
#print axioms opening_late_hit_yields_whole_domain_hit
#print axioms accepted_opening_prefix_or_shared_failure
end AspisV8.AuthenticatedEarlyC1Targets
