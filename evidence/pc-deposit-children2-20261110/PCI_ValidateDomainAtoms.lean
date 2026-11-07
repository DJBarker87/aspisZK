import PCI_ValidateField
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateDomainAtoms
open PCA PCI_ValidateWords PCI_ValidateField
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

theorem word_bound (x : UInt32) (h : x.toNat<2147483647) :
    (word x).val<2147483647 := h

theorem sub_bound (a b : UInt32) :
    (word (PCC.fieldSub a b)).val<2147483647 := word_bound _ (sub_canonical a b)

theorem index_bound (d : Digest) (h : PCC.canonical d=true) (i : Nat) (bound : i<8) :
    (word d[i]).val<2147483647 := word_bound _ (canonical_index d h i bound)

#print axioms canonical_member
#print axioms canonical_index
#print axioms word_bound
#print axioms sub_bound
#print axioms index_bound
end PCI_ValidateDomainAtoms
