import PCI_ValidateField
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateDomains
open PCA PCI_ValidateWords PCI_ValidateField

def Entered (w : PairWitness) : Prop :=
  PCC.canonical w.firstCommitment=true ∧ PCC.canonical w.secondCommitment=true ∧
  w.secondOccupied.toNat<2147483647 ∧ w.secondOccupancyInverse.toNat<2147483647

theorem canonical_member (d : Digest) (h : PCC.canonical d=true)
    (x : UInt32) (member : x∈d.toList) : x.toNat<2147483647 := by
  change d.toList.all (fun limb => decide (limb.toNat<2147483647))=true at h
  exact of_decide_eq_true ((List.all_eq_true.mp h) x member)

theorem canonical_index (d : Digest) (h : PCC.canonical d=true)
    (i : Nat) (bound : i<8) : d[i].toNat<2147483647 := by
  have hb : i<d.toList.length := by simpa using bound
  have hm : d.toList[i]∈d.toList := List.getElem_mem hb
  apply canonical_member d h
  simpa using hm

def Domain (w : PairWitness) : Prop :=
  (word w.secondOccupied).val<2147483647 ∧
  (word (PCC.fieldSub w.secondOccupied 1)).val<2147483647 ∧
  (word w.secondCommitment[7]).val<2147483647 ∧
  (word w.secondOccupancyInverse).val<2147483647 ∧
  (word (PCC.fieldSub 1 w.secondOccupied)).val<2147483647 ∧
  ∀ limb∈w.secondCommitment.toList, (word limb).val<2147483647

theorem entered_domains (w : PairWitness) (h : Entered w) : Domain w := by
  obtain ⟨_,hc,ho,hi⟩ := h
  unfold Domain
  simp only [word_value]
  exact ⟨ho,sub_canonical _ _,canonical_index _ hc 7 (by decide),hi,
    sub_canonical _ _,fun limb member => canonical_member _ hc limb member⟩

/-- Domain evidence is unconditional at the row root: rejected gates make no
    field call; every entered field call has canonical SAME operands. -/
theorem reached_domains (w : PairWitness) : ¬Entered w ∨ Domain w := by
  by_cases h : Entered w
  · exact .inr (entered_domains w h)
  · exact .inl h

#print axioms canonical_member
#print axioms canonical_index
#print axioms entered_domains
#print axioms reached_domains
end PCI_ValidateDomains
