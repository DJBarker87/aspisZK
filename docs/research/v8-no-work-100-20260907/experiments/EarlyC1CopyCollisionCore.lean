import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod

/-! Finite collision sets for a family fixed before two sequential challenges.
The second polynomial may depend on the first challenge; family selection
may depend on both. No actual transcript law or acceptance premise is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.EarlyC1CopyCollisionCore
open Polynomial Finset
noncomputable section
variable {K M : Type*} [Field K]

def rootsIn (P : K[X]) (domain : Finset K) : Finset K := by
  classical
  exact domain.filter fun x => P ≠ 0 ∧ P.eval x = 0

theorem mem_rootsIn (P : K[X]) (domain : Finset K) (x : K) :
    x ∈ rootsIn P domain ↔ x ∈ domain ∧ P ≠ 0 ∧ P.eval x = 0 := by
  classical
  simp only [rootsIn, Finset.mem_filter]

theorem rootsIn_card (P : K[X]) (domain : Finset K) :
    (rootsIn P domain).card ≤ P.natDegree := by
  classical
  by_cases nonzero : P ≠ 0
  · apply Polynomial.card_le_degree_of_subset_roots
    intro x member
    exact (Polynomial.mem_roots nonzero).mpr ((mem_rootsIn P domain x).mp member).2.2
  · simp [rootsIn, nonzero]

def familyRoots (family : Finset M) (polynomial : M → K[X])
    (domain : Finset K) : Finset K := by
  classical
  exact family.biUnion fun member => rootsIn (polynomial member) domain

theorem mem_familyRoots (family : Finset M) (polynomial : M → K[X])
    (domain : Finset K) (x : K) :
    x ∈ familyRoots family polynomial domain ↔
      ∃ member ∈ family, x ∈ domain ∧ polynomial member ≠ 0 ∧
        (polynomial member).eval x = 0 := by
  classical
  simp only [familyRoots, Finset.mem_biUnion, mem_rootsIn]

theorem familyRoots_card (family : Finset M) (polynomial : M → K[X])
    (domain : Finset K) (degree : Nat)
    (bound : ∀ member ∈ family, polynomial member ≠ 0 →
      (polynomial member).natDegree ≤ degree) :
    (familyRoots family polynomial domain).card ≤ family.card * degree := by
  classical
  calc
    _ ≤ ∑ member ∈ family, (rootsIn (polynomial member) domain).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _member ∈ family, degree := by
      apply Finset.sum_le_sum
      intro member present
      by_cases nonzero : polynomial member ≠ 0
      · exact (rootsIn_card _ _).trans (bound member present nonzero)
      · simp [rootsIn, nonzero]
    _ = _ := by simp

/-- A single pair event: its first part is fixed before lambda; each second
slice is fixed after lambda and before chi. The union does not choose a
family member early or count only a provider's successful paths. -/
def sequentialRoots (family : Finset M) (first : M → K[X])
    (second : M → K → K[X]) (lambdas chis : Finset K) : Finset (K × K) := by
  classical
  exact (familyRoots family first lambdas ×ˢ chis) ∪
    lambdas.biUnion (fun lambda => {lambda} ×ˢ
      familyRoots family (fun member => second member lambda) chis)

theorem mem_sequentialRoots (family : Finset M) (first : M → K[X])
    (second : M → K → K[X]) (lambdas chis : Finset K) (lambda chi : K) :
    (lambda, chi) ∈ sequentialRoots family first second lambdas chis ↔
      lambda ∈ lambdas ∧ chi ∈ chis ∧
        (lambda ∈ familyRoots family first lambdas ∨
          chi ∈ familyRoots family (fun member => second member lambda) chis) := by
  classical
  simp only [sequentialRoots, Finset.mem_union, Finset.mem_product,
    Finset.mem_biUnion, Finset.mem_singleton]
  constructor
  · rintro (⟨firstRoot, chiMember⟩ | ⟨other, otherMember, equal, secondRoot⟩)
    · obtain ⟨member, _, lambdaMember, _, _⟩ :=
        (mem_familyRoots family first lambdas lambda).mp firstRoot
      exact ⟨lambdaMember, chiMember, Or.inl firstRoot⟩
    · subst other
      obtain ⟨member, _, chiMember, _, _⟩ :=
        (mem_familyRoots family (fun member => second member lambda) chis chi).mp secondRoot
      exact ⟨otherMember, chiMember, Or.inr secondRoot⟩
  · rintro ⟨lambdaMember, chiMember, firstRoot | secondRoot⟩
    · exact Or.inl ⟨firstRoot, chiMember⟩
    · exact Or.inr ⟨lambda, lambdaMember, rfl, secondRoot⟩

theorem sequentialRoots_card (family : Finset M) (first : M → K[X])
    (second : M → K → K[X]) (lambdas chis : Finset K) (firstDegree secondDegree : Nat)
    (firstBound : ∀ member ∈ family, first member ≠ 0 →
      (first member).natDegree ≤ firstDegree)
    (secondBound : ∀ lambda ∈ lambdas, ∀ member ∈ family, second member lambda ≠ 0 →
      (second member lambda).natDegree ≤ secondDegree) :
    (sequentialRoots family first second lambdas chis).card ≤
      family.card * firstDegree * chis.card + lambdas.card * (family.card * secondDegree) := by
  classical
  have firstCap := familyRoots_card family first lambdas firstDegree firstBound
  have secondCap : ∀ lambda ∈ lambdas,
      (familyRoots family (fun member => second member lambda) chis).card ≤
        family.card * secondDegree := fun lambda member =>
    familyRoots_card family (fun member => second member lambda) chis secondDegree
      (secondBound lambda member)
  unfold sequentialRoots
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · rw [Finset.card_product]
    exact Nat.mul_le_mul_right chis.card firstCap
  · calc
      _ ≤ ∑ lambda ∈ lambdas,
          ({lambda} ×ˢ familyRoots family (fun member => second member lambda) chis).card :=
        Finset.card_biUnion_le
      _ = ∑ lambda ∈ lambdas,
          (familyRoots family (fun member => second member lambda) chis).card := by simp
      _ ≤ ∑ _lambda ∈ lambdas, family.card * secondDegree :=
        Finset.sum_le_sum secondCap
      _ = _ := by simp

/-- Every adaptive selection, including one made after both challenges,
is covered by the same sets. A selection outside family is not silently
turned into an in-family collision event. -/
theorem adaptive_selection_covered (family : Finset M) (first : M → K[X])
    (second : M → K → K[X]) (lambdas chis : Finset K)
    (select : K → K → M) (lambda chi : K)
    (lambdaMember : lambda ∈ lambdas) (chiMember : chi ∈ chis)
    (member : select lambda chi ∈ family)
    (collision : (first (select lambda chi) ≠ 0 ∧
        (first (select lambda chi)).eval lambda = 0) ∨
      (second (select lambda chi) lambda ≠ 0 ∧
        (second (select lambda chi) lambda).eval chi = 0)) :
    (lambda,chi) ∈ sequentialRoots family first second lambdas chis := by
  apply (mem_sequentialRoots family first second lambdas chis lambda chi).mpr
  refine ⟨lambdaMember, chiMember, ?_⟩
  rcases collision with firstHit | secondHit
  · exact Or.inl ((mem_familyRoots family first lambdas lambda).mpr
      ⟨select lambda chi, member, lambdaMember, firstHit⟩)
  · exact Or.inr ((mem_familyRoots family (fun m => second m lambda) chis chi).mpr
      ⟨select lambda chi, member, chiMember, secondHit⟩)

#print axioms mem_rootsIn
#print axioms rootsIn_card
#print axioms mem_familyRoots
#print axioms familyRoots_card
#print axioms mem_sequentialRoots
#print axioms sequentialRoots_card
#print axioms adaptive_selection_covered
end
end AspisV8.EarlyC1CopyCollisionCore
