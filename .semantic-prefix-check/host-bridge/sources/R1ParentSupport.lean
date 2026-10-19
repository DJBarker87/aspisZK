import R1NaturalProjection
import R1RepeatedLift
import Lean.Elab.Tactic.Omega

/-! Finite support bookkeeping for the parent map of a four-lane flat vector.
These are index and cardinality identities only; they make no decoder,
protocol, or cryptographic claim. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

open scoped BigOperators

local instance {n : Nat} : DecidableEq (Fin n) := Classical.decEq _

/-- Parent positions represented by a flat finite support. -/
def parentSupport {n : Nat} (M : Finset (Fin (4 * n))) : Finset (Fin n) :=
  M.image parentIndex

/-- The union of all four flat coordinates above every parent in `S`. -/
def fullQuartetSet {n : Nat} (S : Finset (Fin n)) : Finset (Fin (4 * n)) :=
  S.biUnion fun v => Finset.univ.image (childIndex v)

/-- The flat full-quartet set is the image of the abstract repeated support
under the existing parent-slot equivalence. -/
theorem fullQuartetSet_eq_repeatedSupport_image {n : Nat}
    (S : Finset (Fin n)) :
    fullQuartetSet S =
      (repeatedSupport S).image (fibreIndexEquiv n) := by
  ext k
  simp [fullQuartetSet, AspisR1.repeatedSupport, fibreIndexEquiv]

/-- Every full-quartet set has exactly four coordinates per parent. -/
theorem fullQuartetSet_card {n : Nat} (S : Finset (Fin n)) :
    (fullQuartetSet S).card = 4 * S.card := by
  rw [fullQuartetSet_eq_repeatedSupport_image]
  rw [Finset.card_image_of_injective _ (fibreIndexEquiv n).injective]
  exact repeated_support_card S

/-- The parent map sends every coordinate in a full quartet set back into
the parent support. -/
theorem parentIndex_mem_of_mem_fullQuartetSet {n : Nat}
    (S : Finset (Fin n)) {k : Fin (4 * n)}
    (hk : k ∈ fullQuartetSet S) : parentIndex k ∈ S := by
  rcases Finset.mem_biUnion.mp hk with ⟨v, hv, hslots⟩
  rcases Finset.mem_image.mp hslots with ⟨slot, _hslot, hindex⟩
  rw [← hindex]
  simpa using hv

/-- Each flat support is contained in the full quartets above its parent
image. -/
theorem mem_fullQuartetSet_parentSupport {n : Nat}
    (M : Finset (Fin (4 * n))) (k : Fin (4 * n)) (hk : k ∈ M) :
    k ∈ fullQuartetSet (parentSupport M) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨parentIndex k, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  · apply Finset.mem_image.mpr
    exact ⟨slotIndex k, Finset.mem_univ _, childIndex_parentIndex_slotIndex k⟩

theorem support_subset_fullQuartets {n : Nat}
    (M : Finset (Fin (4 * n))) :
    M ⊆ fullQuartetSet (parentSupport M) := by
  intro k hk
  exact mem_fullQuartetSet_parentSupport M k hk

/-- The cardinality of a flat support is at most four times the number of
distinct parents it touches. -/
theorem support_card_le_four_parentSupport_card {n : Nat}
    (M : Finset (Fin (4 * n))) :
    M.card ≤ 4 * (parentSupport M).card := by
  calc
    M.card ≤ (fullQuartetSet (parentSupport M)).card :=
      Finset.card_le_card (support_subset_fullQuartets M)
    _ = 4 * (parentSupport M).card := fullQuartetSet_card _

/-- A support of at least 9558 flat positions touches at least 2390 distinct
parents. -/
theorem parentSupport_card_ge_2390_of_card_ge_9558 {n : Nat}
    (M : Finset (Fin (4 * n))) (hM : 9558 ≤ M.card) :
    2390 ≤ (parentSupport M).card := by
  have hbound := support_card_le_four_parentSupport_card M
  omega

/-- Concrete-width arithmetic instance for the R1 four-lane support. -/
theorem parentSupport_card_ge_2390_65536
    (M : Finset (Fin (4 * 65536))) (hM : 9558 ≤ M.card) :
    2390 ≤ (parentSupport M).card :=
  parentSupport_card_ge_2390_of_card_ge_9558 M hM

#print axioms fullQuartetSet_eq_repeatedSupport_image
#print axioms fullQuartetSet_card
#print axioms parentIndex_mem_of_mem_fullQuartetSet
#print axioms mem_fullQuartetSet_parentSupport
#print axioms support_subset_fullQuartets
#print axioms support_card_le_four_parentSupport_card
#print axioms parentSupport_card_ge_2390_of_card_ge_9558
#print axioms parentSupport_card_ge_2390_65536

end AspisR1

end
