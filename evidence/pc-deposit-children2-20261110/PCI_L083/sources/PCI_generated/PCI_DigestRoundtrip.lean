import PCI_DigestCarrier
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DigestRoundtrip
open PCI_DigestCarrier PCI_ValidateWords PCI_ValidateCarrier

def encode (d : PCA.Digest) : Array U32 8#usize :=
  ⟨d.toList.map word,by simp only [List.length_map,Vector.length_toList];rfl⟩

theorem roundtrip (d : PCA.Digest) : digest (encode d)=d := by
  apply Vector.toList_inj.mp
  simp only [digest,encode,Vector.toList,List.toList_toArray,List.map_map,Function.comp_def,read_word]
  exact List.map_id _

theorem canonical (d : PCA.Digest) :
    PCI_ArrayCanonical.model (encode d)=PCC.canonical d := by
  rw [PCI_DigestCarrier.canonical,roundtrip]

#print axioms roundtrip
#print axioms canonical
end PCI_DigestRoundtrip
