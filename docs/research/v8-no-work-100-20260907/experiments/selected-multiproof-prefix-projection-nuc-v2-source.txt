import MinimalMultiproofPaths
import AuthenticatedPhaseWords

/-! The selected q22 multiproof supplies actual paths, not path premises.
Both phase-specific prefix binders are applied at the original record ordinal.
Their bad cases share one raw-log collision predicate; unresolved C1 and C2
targets remain explicit. No probability, byte-loop refinement, challenge law,
or assumption that a root alone fixes its disclosed word is introduced.

C1 and C2 answer prefixes are separate inputs. Their intended chronological
cutoffs (before lambda/chi, and after lambda/chi but before OOD respectively)
must be supplied by the source execution; no later prefix replaces early C1.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedMultiproofPrefixProjection
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding AspisPool.V7MerkleCanonicalOpening
open AspisPool.V7MerklePartialPathExtractor
open AspisV8.MinimalMultiproofPaths
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.AuthenticatedPhaseWords
noncomputable section

/-- Convert the constructed bottom-up lists into the existing paired-opening
type. Both complete authentication traces are derived from the multiproof log. -/
theorem accepted_opening_at (view : RawHashInput → Digest208) (roots : Digests)
    (query : Fin 22 → Position) (records : Fin 22 → Record)
    (frontier : List Digests) (nodeLog : OrderedRawQueryLog)
    (accepted : Accepted view roots query records frontier nodeLog) (i : Fin 22) :
    ∃ opening : PairedOpening,
      opening.position = query i ∧ opening.c1Value = (records i).c1 ∧
      opening.c2Value = (records i).c2 ∧ opening.sharedSalt = (records i).salt ∧
      foldPath view opening.position (c1DisclosedLeafDigest view opening)
        opening.c1Siblings = roots 0 ∧
      foldPath view opening.position (c2DisclosedLeafDigest view opening)
        opening.c2Siblings = roots 1 ∧
      TraceIncludedInLog (openingInputTrace view opening.position
        (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings)
        (leafLog query records ++ nodeLog) ∧
      TraceIncludedInLog (openingInputTrace view opening.position
        (.c2Leaf opening.c2Value opening.sharedSalt) opening.c2Siblings)
        (leafLog query records ++ nodeLog) := by
  obtain ⟨paths, lengths, rootExact, covered⟩ :=
    accepted_q22_paths view roots query records frontier nodeLog accepted i
  let opening : PairedOpening :=
    { position := query i
      c1Value := (records i).c1
      c2Value := (records i).c2
      sharedSalt := (records i).salt
      c1Siblings := siblingPathOfList (paths 0) (lengths 0)
      c2Siblings := siblingPathOfList (paths 1) (lengths 1) }
  have leaf0 : leafInput (records i) 0 =
      serialize (.c1Leaf (records i).c1 (records i).salt) := rfl
  have leaf1 : leafInput (records i) 1 =
      serialize (.c2Leaf (records i).c2 (records i).salt) := rfl
  refine ⟨opening, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change foldPathAux view (query i).val
      (view (serialize (.c1Leaf (records i).c1 (records i).salt)))
      (List.ofFn (siblingPathOfList (paths 0) (lengths 0))) = roots 0
    rw [ofFn_siblingPathOfList]
    exact leaf0 ▸ rootExact 0
  · change foldPathAux view (query i).val
      (view (serialize (.c2Leaf (records i).c2 (records i).salt)))
      (List.ofFn (siblingPathOfList (paths 1) (lengths 1))) = roots 1
    rw [ofFn_siblingPathOfList]
    exact leaf1 ▸ rootExact 1
  · change TraceIncludedInLog
      (serialize (.c1Leaf (records i).c1 (records i).salt) ::
        foldPathInputTrace view (query i).val
          (view (serialize (.c1Leaf (records i).c1 (records i).salt)))
          (List.ofFn (siblingPathOfList (paths 0) (lengths 0)))) _
    rw [ofFn_siblingPathOfList]
    exact leaf0 ▸ covered 0
  · change TraceIncludedInLog
      (serialize (.c2Leaf (records i).c2 (records i).salt) ::
        foldPathInputTrace view (query i).val
          (view (serialize (.c2Leaf (records i).c2 (records i).salt)))
          (List.ofFn (siblingPathOfList (paths 1) (lengths 1)))) _
    rw [ofFn_siblingPathOfList]
    exact leaf1 ▸ covered 1

/-- The resolver is fixed from one phase prefix; the queried ordinal can be
chosen later. The witnessed fresh input is located in the shared full log. -/
def LateTargetHit (view : RawHashInput → Digest208)
    (resolver : Position → Option Digest208) (prefixLog fullLog : OrderedRawQueryLog)
    (query : Fin 22 → Position) : Prop :=
  ∃ i : Fin 22, ∃ target, resolver (query i) = some target ∧
    ∃ input ∈ fullLog, input ∉ prefixLog ∧ view input = target

def C1LateTargetHit (view : RawHashInput → Digest208) (prefixRecords : AnswerPrefix)
    (root : Digest208) (fullLog : OrderedRawQueryLog) (query : Fin 22 → Position) : Prop :=
  LateTargetHit view
    (firstUnresolvedC1Target (frozenView prefixRecords) (rawPrefix prefixRecords) root)
    (rawPrefix prefixRecords) fullLog query

def C2LateTargetHit (view : RawHashInput → Digest208) (prefixRecords : AnswerPrefix)
    (root : Digest208) (fullLog : OrderedRawQueryLog) (query : Fin 22 → Position) : Prop :=
  LateTargetHit view
    (firstUnresolvedC2Target (frozenView prefixRecords) (rawPrefix prefixRecords) root)
    (rawPrefix prefixRecords) fullLog query

def ProjectionsAt (c1Prefix c2Prefix : AnswerPrefix) (roots : Digests)
    (query : Fin 22 → Position) (records : Fin 22 → Record) (i : Fin 22) : Prop :=
  (prefixWords c1Prefix (roots 0)).c1[(query i).val]? =
      some ⟨(records i).c1, (records i).salt⟩ ∧
  (prefixWords c2Prefix (roots 1)).c2[(query i).val]? =
      some ⟨(records i).c2, (records i).salt⟩

/-- Per-ordinal projection or explicit shared failure. Paths and coverage
are obtained above, not supplied as independent authentication assumptions. -/
theorem accepted_projection_at_or_failure
    (view : RawHashInput → Digest208) (roots : Digests)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (query : Fin 22 → Position) (records : Fin 22 → Record)
    (frontier : List Digests) (nodeLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog (leafLog query records ++ nodeLog) fullLog)
    (accepted : Accepted view roots query records frontier nodeLog) (i : Fin 22) :
    ProjectionsAt c1Prefix c2Prefix roots query records i ∨
      RawLogTruncatedDigestCollision view fullLog ∨
      C1LateTargetHit view c1Prefix (roots 0) fullLog query ∨
      C2LateTargetHit view c2Prefix (roots 1) fullLog query := by
  obtain ⟨opening, position, c1Value, c2Value, salt, root0, root1, trace0, trace1⟩ :=
    accepted_opening_at view roots query records frontier nodeLog accepted i
  have covered0 : TraceIncludedInLog (openingInputTrace view opening.position
      (.c1Leaf opening.c1Value opening.sharedSalt) opening.c1Siblings) fullLog :=
    fun input member => callsIncluded input (trace0 input member)
  have covered1 : TraceIncludedInLog (openingInputTrace view opening.position
      (.c2Leaf opening.c2Value opening.sharedSalt) opening.c2Siblings) fullLog :=
    fun input member => callsIncluded input (trace1 input member)
  rcases accepted_opening_prefix_or_late_target_or_collision c1Prefix (roots 0)
      view fullLog opening c1Answers c1Included root0 covered0 with proj0 | late0 | collision
  · rcases accepted_c2_opening_prefix_or_late_target_or_collision c2Prefix (roots 1)
        view fullLog opening c2Answers c2Included root1 covered1 with proj1 | late1 | collision
    · left
      unfold ProjectionsAt
      exact ⟨by simpa only [position, c1Value, salt] using proj0,
        by simpa only [position, c2Value, salt] using proj1⟩
    · obtain ⟨target, chosen, input, member, fresh, digest⟩ := late1
      apply Or.inr (Or.inr (Or.inr ?_))
      exact ⟨i, target, by simpa only [position] using chosen,
        input, covered1 input member, fresh, digest⟩
    · exact Or.inr (Or.inl collision)
  · obtain ⟨target, chosen, input, member, fresh, digest⟩ := late0
    apply Or.inr (Or.inr (Or.inl ?_))
    exact ⟨i, target, by simpa only [position] using chosen,
      input, covered0 input member, fresh, digest⟩
  · exact Or.inr (Or.inl collision)

/-- One symbolic bad alternative or ALL 22 projections, preserving record
ordinal, both packed leaf values, and the shared salt. No event receives a
factor 22 or a probability here. Prefix nesting/timing is not inferred from
the two trace-inclusion hypotheses. -/
theorem accepted_all_projections_or_shared_failure
    (view : RawHashInput → Digest208) (roots : Digests)
    (c1Prefix c2Prefix : AnswerPrefix) (fullLog : OrderedRawQueryLog)
    (query : Fin 22 → Position) (records : Fin 22 → Record)
    (frontier : List Digests) (nodeLog : OrderedRawQueryLog)
    (c1Answers : ∀ record ∈ c1Prefix, view record.1 = record.2)
    (c2Answers : ∀ record ∈ c2Prefix, view record.1 = record.2)
    (c1Included : TraceIncludedInLog (rawPrefix c1Prefix) fullLog)
    (c2Included : TraceIncludedInLog (rawPrefix c2Prefix) fullLog)
    (callsIncluded : TraceIncludedInLog (leafLog query records ++ nodeLog) fullLog)
    (accepted : Accepted view roots query records frontier nodeLog) :
    RawLogTruncatedDigestCollision view fullLog ∨
      C1LateTargetHit view c1Prefix (roots 0) fullLog query ∨
      C2LateTargetHit view c2Prefix (roots 1) fullLog query ∨
      ∀ i : Fin 22, ProjectionsAt c1Prefix c2Prefix roots query records i := by
  classical
  by_cases collision : RawLogTruncatedDigestCollision view fullLog
  · exact Or.inl collision
  by_cases late0 : C1LateTargetHit view c1Prefix (roots 0) fullLog query
  · exact Or.inr (Or.inl late0)
  by_cases late1 : C2LateTargetHit view c2Prefix (roots 1) fullLog query
  · exact Or.inr (Or.inr (Or.inl late1))
  apply Or.inr (Or.inr (Or.inr ?_))
  intro i
  rcases accepted_projection_at_or_failure view roots c1Prefix c2Prefix fullLog
      query records frontier nodeLog c1Answers c2Answers c1Included c2Included
      callsIncluded accepted i with projection | bad | bad | bad
  · exact projection
  · exact False.elim (collision bad)
  · exact False.elim (late0 bad)
  · exact False.elim (late1 bad)

#print axioms accepted_opening_at
#print axioms accepted_projection_at_or_failure
#print axioms accepted_all_projections_or_shared_failure
end
end AspisV8.SelectedMultiproofPrefixProjection
