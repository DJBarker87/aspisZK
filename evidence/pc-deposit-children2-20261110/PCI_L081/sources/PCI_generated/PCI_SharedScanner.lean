import NFY_Part053
import PCI_DigestCarrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_SharedScanner
open PCI_DigestCarrier PCI_ValidateCarrier
attribute [local instance] Classical.propDecidable

theorem domain (d : Array U32 8#usize) :
    PCC.canonical (digest d)=true ↔ NBD_DigestInduction.Canonical d := by
  have hd : d.val.length=8 := d.property
  constructor
  · intro h j
    have hm : readWord d.val[j.val] ∈ (digest d).toList := by
      change readWord d.val[j.val] ∈ d.val.map readWord
      exact List.mem_map.mpr ⟨d.val[j.val],List.getElem_mem _,rfl⟩
    have ht := PCI_ValidateDomainAtoms.canonical_member (digest d) h _ hm
    simpa only [read_value] using ht
  · intro h
    change (d.val.map readWord).all (fun x => decide (x.toNat<2147483647))=true
    apply List.all_eq_true.mpr
    intro x hx
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hw
    have hi8 : i<8 := by have hd:=d.property;scalar_tac
    have ht := h ⟨i,hi8⟩
    rw [he] at ht
    simpa only [decide_eq_true_eq,read_value] using ht

theorem result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical d=
      ok (PCC.canonical (digest d)) := by
  rw [NFY_NED_ScannerCohorts.profile_result]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (domain d).symm

#print axioms domain
#print axioms result
end PCI_SharedScanner
