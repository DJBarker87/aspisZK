import AuthenticatedEarlyC1Prefix

/-! A checked authenticated support gives the ORIGINAL optional early C1
projection, or an explicit later-target/collision event. The support may be
proper: no hypothesis requires every committed leaf to be present early.
Producing this many authenticated values from actual rewinds is not proved. -/
set_option autoImplicit false
set_option maxRecDepth 100
set_option maxHeartbeats 100000
namespace AspisV8.AuthenticatedEarlyC1Projection
open AspisV8.AuthenticatedEarlyC1Prefix AspisV8.EarlyC1Projection
open AspisV8.EarlyC1Specialization AspisV8.EarlyC1LateProjection
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding AspisPool.V7ExtractedLaneWords
open AspisPool.V7PackedFibreTowerBridge AspisV5ComponentCQM31TowerExact

noncomputable local instance : Fintype (Fin 262144) := explicit_instance

/-- Canonical parser success is required at authenticated coordinates;
the unchecked zero-default totalization cannot satisfy this premise. -/
def DisclosedC1Matches (p : C1Messages) (opening : PairedOpening)
    (fibre : Fin 262144) : Prop :=
  ∀ column slot, ∃ decoded,
    decodeC1EntryExact opening.c1Value slot column = some decoded ∧
    embedM31Exact decoded = fibreEncode (p column) fibre slot

theorem projected_canonical_fibre_matches
    (records : AnswerPrefix) (root : Digest208) (opening : PairedOpening)
    (fibre : Fin 262144) (position : opening.position.val = fibre.val)
    (projection : (prefixWords records root).c1[opening.position.val]? =
      some ⟨opening.c1Value, opening.sharedSalt⟩)
    (p : C1Messages) (matching : DisclosedC1Matches p opening fibre) :
    ∀ column, receivedFibres (fixedC1 records root) column fibre =
      fibreEncode (p column) fibre := by
  intro column
  funext slot
  obtain ⟨decoded, parsed, encoded⟩ := matching column slot
  have atFibre : (prefixWords records root).c1[fibre.val]? =
      some ⟨opening.c1Value, opening.sharedSalt⟩ := by
    rw [position] at projection
    exact projection
  have atIndex : (prefixWords records root).c1[
      (fibreIndex (initialIndex fibre slot)).val]? =
      some ⟨opening.c1Value, opening.sharedSalt⟩ := by
    rw [fibreIndex_initialIndex]
    exact atFibre
  have parsedIndex : decodeC1EntryExact opening.c1Value
      (fibreSlot (initialIndex fibre slot)) column = some decoded := by
    rw [fibreSlot_initialIndex]
    exact parsed
  have value := c1_received_of_exact_projection (prefixWords records root)
    (initialIndex fibre slot) column ⟨opening.c1Value, opening.sharedSalt⟩ decoded
    atIndex parsedIndex
  exact value.trans encoded

theorem authenticated_support_identifies_or_bad
    (records : AnswerPrefix) (root : Digest208)
    (view : RawHashInput → Digest208) (fullLog : OrderedRawQueryLog)
    (openings : Fin 262144 → PairedOpening) (S : Finset (Fin 262144))
    (p : Fin 29 → Message)
    (answers : ∀ record ∈ records, view record.1 = record.2)
    (included : TraceIncludedInLog (rawPrefix records) fullLog)
    (size : 245609 ≤ S.card)
    (positions : ∀ fibre ∈ S, (openings fibre).position.val = fibre.val)
    (accepted : ∀ fibre ∈ S, foldPath view (openings fibre).position
      (c1DisclosedLeafDigest view (openings fibre)) (openings fibre).c1Siblings = root)
    (covered : ∀ fibre ∈ S, TraceIncludedInLog
      (openingInputTrace view (openings fibre).position
        (.c1Leaf (openings fibre).c1Value (openings fibre).sharedSalt)
        (openings fibre).c1Siblings) fullLog)
    (matching : ∀ fibre ∈ S, DisclosedC1Matches (c1Projection p) (openings fibre) fibre) :
    fixedEarlyC1 records root = some (c1Projection p) ∨
      (∃ fibre ∈ S, OpeningLateTargetHit view records root (openings fibre)) ∨
      RawLogTruncatedDigestCollision view fullLog := by
  classical
  by_cases collision : RawLogTruncatedDigestCollision view fullLog
  · exact Or.inr (Or.inr collision)
  by_cases late : ∃ fibre ∈ S, OpeningLateTargetHit view records root (openings fibre)
  · exact Or.inr (Or.inl late)
  apply Or.inl
  apply identify
  have subset : S ⊆ support fibreEncode (receivedFibres (fixedC1 records root))
      (c1Projection p) := by
    intro fibre member
    have alternatives := accepted_opening_prefix_or_late_target_or_collision
      records root view fullLog (openings fibre) answers included
      (accepted fibre member) (covered fibre member)
    have projection := alternatives.resolve_right (by
      rintro (hit | collided)
      · exact late ⟨fibre, member, hit⟩
      · exact collision collided)
    have values := projected_canonical_fibre_matches records root (openings fibre)
      fibre (positions fibre member) projection (c1Projection p) (matching fibre member)
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact values
  exact size.trans (Finset.card_le_card subset)

#print axioms projected_canonical_fibre_matches
#print axioms authenticated_support_identifies_or_bad
end AspisV8.AuthenticatedEarlyC1Projection
