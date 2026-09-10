import EarlyC1CopyCollisionCore
import EarlyC1Family
import SelectedCopyAliasQM31

/-! Actual pre-lambda C1 family -> selected copy collision sets.
The family is defined from received C1 alone. Every table is the literal
transpose of its first sixteen message columns; C2, lambda, chi, and a
provider are not inputs to this construction. This is covered-class
accounting, not acceptance-to-family or an efficient extractor theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.EarlyC1CopyCollision
open Polynomial Finset
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7ExtractedLaneWords AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7FixedWidth29TupleList
open AspisV6Width29CorrelatedAgreement
open AspisV8.EarlyC1Family AspisV8.EarlyC1LateProjection
open AspisV8.SelectedWeightedCopyCore AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedCopyAliases AspisV8.SelectedCopyAliasCore
open AspisV8.SelectedCopyAliasQM31 AspisV8.EarlyC1CopyCollisionCore
noncomputable section
abbrev K := QM31Exact

/-- Total copy-table interface. Columns beyond the sixteen semantic columns
are unused by every source tuple pattern, not assumed zero in C1. -/
def memberTable (p : C1InitialMessages) : Table K :=
  fun row column => if bounded : column < 16 then p ⟨column, by omega⟩ row else 0

theorem memberTable_read (p : C1InitialMessages) (row : Fin 1024) (column : Fin 16) :
    memberTable p row column.val = p ⟨column.val, by omega⟩ row := by
  simp only [memberTable, dif_pos column.isLt]

/-- The source's fourteen patterns only read this exact early projection.
Public last-limb offsets remain present and are not witness cells. -/
theorem pattern_member_read (p : C1InitialMessages) (endpoint : Endpoint)
    (limb : Fin 16) (live : limb.val < (sourcePatterns endpoint.pattern).width) :
    patternLimb (memberTable p) endpoint limb =
      p ⟨(sourcePatterns endpoint.pattern).start + limb.val,
        (pattern_read_in_range endpoint.pattern limb live).trans_le (by decide)⟩ endpoint.row +
      if limb.val + 1 = (sourcePatterns endpoint.pattern).width then
        ((sourcePatterns endpoint.pattern).lastOffset : K) else 0 := by
  simp only [patternLimb, live, if_true, memberTable,
    dif_pos (pattern_read_in_range endpoint.pattern limb live)]

theorem late_projection_read (p : Fin 29 → EarlyC1Projection.Message)
    (row : Fin 1024) (column : Fin 16) :
    memberTable (c1Projection p) row column.val =
      p (c1LaneIndex ⟨column.val, by omega⟩) row := by
  rw [memberTable_read]
  rfl

def firstPolynomial (variant : Variant) (appendIndex : Nat)
    (p : C1InitialMessages) : K[X] := lambdaWitness (memberTable p) variant appendIndex

def secondPolynomial (variant : Variant) (appendIndex : Nat)
    (p : C1InitialMessages) (lambda : K) : K[X] :=
  chiWitness (memberTable p) variant appendIndex lambda

theorem first_degree (variant : Variant) (appendIndex : Nat) (p : C1InitialMessages) :
    (firstPolynomial variant appendIndex p).natDegree ≤
      16 * (activeLinks variant appendIndex).card := by
  simpa only [firstPolynomial, lambdaWitness, polyMultiset_card, max_self] using
    lambdaError_degree
      (polyMultiset (memberTable p) variant appendIndex producer)
      (polyMultiset (memberTable p) variant appendIndex consumer) 16
      (polyMultiset_degree _ _ _ _) (polyMultiset_degree _ _ _ _)

theorem second_degree (variant : Variant) (appendIndex : Nat)
    (p : C1InitialMessages) (lambda : K)
    (nonzero : secondPolynomial variant appendIndex p lambda ≠ 0) :
    (secondPolynomial variant appendIndex p lambda).natDegree ≤
      2 * (activeLinks variant appendIndex).card - 1 := by
  have degree := chiError_degree
    (valueMultiset (memberTable p) variant appendIndex producer lambda)
    (valueMultiset (memberTable p) variant appendIndex consumer lambda) nonzero
  simp only [valueMultiset_card] at degree
  change (secondPolynomial variant appendIndex p lambda).natDegree <
    (activeLinks variant appendIndex).card + (activeLinks variant appendIndex).card at degree
  omega

def lambdaCollisions (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (domain : Finset K) : Finset K :=
  familyRoots (family c1) (firstPolynomial variant appendIndex) domain

def chiCollisions (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambda : K) (domain : Finset K) : Finset K :=
  familyRoots (family c1) (fun p => secondPolynomial variant appendIndex p lambda) domain

theorem lambda_card (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (domain : Finset K) :
    (lambdaCollisions c1 variant appendIndex domain).card ≤
      100 * (16 * (activeLinks variant appendIndex).card) := by
  exact (familyRoots_card (family c1) (firstPolynomial variant appendIndex) domain _
    (fun p _ _ => first_degree variant appendIndex p)).trans
      (Nat.mul_le_mul_right _ (family_card_le_100 c1))

theorem chi_card (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambda : K) (domain : Finset K) :
    (chiCollisions c1 variant appendIndex lambda domain).card ≤
      100 * (2 * (activeLinks variant appendIndex).card - 1) := by
  exact (familyRoots_card (family c1) (fun p => secondPolynomial variant appendIndex p lambda)
    domain _ (fun p _ nonzero => second_degree variant appendIndex p lambda nonzero)).trans
      (Nat.mul_le_mul_right _ (family_card_le_100 c1))

def collisionPairs (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) : Finset (K × K) :=
  sequentialRoots (family c1) (firstPolynomial variant appendIndex)
    (secondPolynomial variant appendIndex) lambdas chis

/-- Literal prerequisites from the selected row/helper theorem. In
particular all four active-row poles remain, even at zero-weight slots. -/
def CopyConditions (p : C1InitialMessages) (variant : Variant) (appendIndex : Nat)
    (lambda chi : K) (helper : Fin 1024 → K) : Prop :=
  (∀ row, selectedBooleanResidual
    (sourceRows (memberTable p) lambda variant appendIndex) helper chi row = 0) ∧
  (∑ row, helper row) = 0 ∧
  (∑ row, inactiveHelper rowActive helper row) = 0 ∧
  (∀ row, rowActive row → NoSlotPole
    (sourceRows (memberTable p) lambda variant appendIndex row) chi)

/-- The chosen member and helper may depend on lambda, chi, C2 and later
observations. Membership is checked against the earlier fixed family;
neither membership nor these source conditions is inferred from acceptance. -/
theorem source_member_covered (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) (lambda chi : K)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (p : C1InitialMessages) (member : p ∈ family c1) (helper : Fin 1024 → K)
    (conditions : CopyConditions p variant appendIndex lambda chi helper) :
    WeightedAliases (memberTable p) variant appendIndex ∨
      (lambda,chi) ∈ collisionPairs c1 variant appendIndex lambdas chis := by
  rcases qm31_source_roots_or_aliases (memberTable p) variant appendIndex lambda chi helper
    conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2 with
    aliases | firstHit | secondHit
  · exact Or.inl aliases
  · right
    exact adaptive_selection_covered (family c1) (firstPolynomial variant appendIndex)
      (secondPolynomial variant appendIndex) lambdas chis (fun _ _ => p) lambda chi
      lambdaMember chiMember member (Or.inl ⟨firstHit.1, firstHit.2.1⟩)
  · right
    exact adaptive_selection_covered (family c1) (firstPolynomial variant appendIndex)
      (secondPolynomial variant appendIndex) lambdas chis (fun _ _ => p) lambda chi
      lambdaMember chiMember member (Or.inr ⟨secondHit.1, secondHit.2.1⟩)

/-- A late width-29 tuple supplies its own support, not the support of the
gamma batch. The existing literal 26+3 projection then establishes actual
membership in the pre-lambda family; no decoder membership is assumed. -/
theorem actual_late_covered (c1 : C1InitialWords) (c2 : C2Received)
    (p : Fin 29 → EarlyC1Projection.Message)
    (own : 38228 ≤
      (width29JointAgreementSet exactInitialEncoder (received29 c1 c2) p).card)
    (variant : Variant) (appendIndex : Nat) (lambdas chis : Finset K) (lambda chi : K)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (helper : Fin 1024 → K)
    (conditions : CopyConditions (c1Projection p) variant appendIndex lambda chi helper) :
    WeightedAliases (memberTable (c1Projection p)) variant appendIndex ∨
      (lambda,chi) ∈ collisionPairs c1 variant appendIndex lambdas chis :=
  source_member_covered c1 variant appendIndex lambdas chis lambda chi lambdaMember chiMember
    (c1Projection p) (actual_late_projection_member c1 c2 p own) helper conditions

theorem collisionPairs_card (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) :
    (collisionPairs c1 variant appendIndex lambdas chis).card ≤
      100 * (16 * (activeLinks variant appendIndex).card) * chis.card +
        lambdas.card * (100 * (2 * (activeLinks variant appendIndex).card - 1)) := by
  have bound := sequentialRoots_card (family c1) (firstPolynomial variant appendIndex)
    (secondPolynomial variant appendIndex) lambdas chis
    (16 * (activeLinks variant appendIndex).card)
    (2 * (activeLinks variant appendIndex).card - 1)
    (fun p _ _ => first_degree variant appendIndex p)
    (fun lambda _ p _ nonzero => second_degree variant appendIndex p lambda nonzero)
  apply bound.trans
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right chis.card
      (Nat.mul_le_mul_right _ (family_card_le_100 c1))
  · exact Nat.mul_le_mul_left lambdas.card
      (Nat.mul_le_mul_right _ (family_card_le_100 c1))

/-- These are the actually in-family failures of this deterministic copy
endpoint, not all accepting proofs. The existential quantifiers retain
arbitrary adaptive member/helper selection. -/
def coveredFailures (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) : Finset (K × K) := by
  classical
  exact (lambdas ×ˢ chis).filter fun pair => ∃ p ∈ family c1,
    ∃ helper : Fin 1024 → K, CopyConditions p variant appendIndex pair.1 pair.2 helper ∧
      ¬ WeightedAliases (memberTable p) variant appendIndex

theorem coveredFailures_subset (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) :
    coveredFailures c1 variant appendIndex lambdas chis ⊆
      collisionPairs c1 variant appendIndex lambdas chis := by
  classical
  intro pair present
  obtain ⟨pairMember, p, member, helper, conditions, failed⟩ := Finset.mem_filter.mp present
  obtain ⟨lambdaMember, chiMember⟩ := Finset.mem_product.mp pairMember
  exact (source_member_covered c1 variant appendIndex lambdas chis pair.1 pair.2
    lambdaMember chiMember p member helper conditions).resolve_left failed

theorem coveredFailures_card (c1 : C1InitialWords) (variant : Variant) (appendIndex : Nat)
    (lambdas chis : Finset K) :
    (coveredFailures c1 variant appendIndex lambdas chis).card ≤
      217600 * chis.card + lambdas.card * 27100 := by
  have bound := (Finset.card_le_card
    (coveredFailures_subset c1 variant appendIndex lambdas chis)).trans
      (collisionPairs_card c1 variant appendIndex lambdas chis)
  have count := active_count_le variant appendIndex
  have firstBound : 100 * (16 * (activeLinks variant appendIndex).card) ≤ 217600 := by omega
  have secondBound : 100 * (2 * (activeLinks variant appendIndex).card - 1) ≤ 27100 := by omega
  exact bound.trans (Nat.add_le_add
    (Nat.mul_le_mul_right chis.card firstBound) (Nat.mul_le_mul_left lambdas.card secondBound))

#print axioms memberTable_read
#print axioms pattern_member_read
#print axioms late_projection_read
#print axioms first_degree
#print axioms second_degree
#print axioms lambda_card
#print axioms chi_card
#print axioms source_member_covered
#print axioms actual_late_covered
#print axioms collisionPairs_card
#print axioms coveredFailures_subset
#print axioms coveredFailures_card
end
end AspisV8.EarlyC1CopyCollision
