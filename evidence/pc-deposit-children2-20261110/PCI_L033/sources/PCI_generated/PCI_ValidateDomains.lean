import PCI_ValidateDomainAtoms
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateDomains
open PCA PCI_ValidateWords PCI_ValidateField PCI_ValidateDomainAtoms

def Entered (w : PairWitness) : Prop :=
  PCC.canonical w.firstCommitment=true ∧ PCC.canonical w.secondCommitment=true ∧
  w.secondOccupied.toNat<2147483647 ∧ w.secondOccupancyInverse.toNat<2147483647


def Domain (w : PairWitness) : Prop :=
  (word w.secondOccupied).val<2147483647 ∧
  (word (PCC.fieldSub w.secondOccupied 1)).val<2147483647 ∧
  (word w.secondCommitment[7]).val<2147483647 ∧
  (word w.secondOccupancyInverse).val<2147483647 ∧
  (word (PCC.fieldSub 1 w.secondOccupied)).val<2147483647 ∧
  ∀ limb∈w.secondCommitment.toList, (word limb).val<2147483647

theorem entered_domains (w : PairWitness) (h : Entered w) : Domain w := by
  obtain ⟨_,hc,ho,hi⟩ := h
  exact ⟨word_bound _ ho,sub_bound _ _,index_bound _ hc 7 (by decide),
    word_bound _ hi,sub_bound _ _,fun limb member => word_bound _ (canonical_member _ hc limb member)⟩

/-- Domain evidence is unconditional at the row root: rejected gates make no
    field call; every entered field call has canonical SAME operands. -/
theorem reached_domains (w : PairWitness) : ¬Entered w ∨ Domain w := by
  by_cases h : Entered w
  · exact .inr (entered_domains w h)
  · exact .inl h

#print axioms entered_domains
#print axioms reached_domains
end PCI_ValidateDomains
