import PSem_Expand
import S1ValuesOwnedAcceptedBytesV1
set_option autoImplicit false
namespace AspisR1.PSem_Values
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical OraclePortCompactDraft

theorem source_expansion (input output updated : Slice U8)
    (call : AspisS1ValuesOwnedInstallation.expandValues input output=ok (.Ok (),updated)) :
    bytesOf updated.val = expand (input.length/16) (bytesOf input.val) := by
  obtain ⟨sameLength,shape,aligned,formula⟩ :=
    AspisS1ValuesOwnedInstallation.accepted_bytes input output updated call
  have inputLength : (bytesOf input.val).length=16*(input.length/16) := by
    simp only [bytesOf,List.length_map]
    change input.length=16*(input.length/16)
    omega
  have outLength : updated.val.length=32*(input.length/16) := by
    change updated.length=32*(input.length/16)
    omega
  have expansionLength := PSem_Expand.expand_length _ _ inputLength
  apply List.ext_getElem?
  intro j
  by_cases bound : j<updated.val.length
  · rw [PSem_Expand.expand_byte _ _ inputLength j (by omega)]
    simp only [bytesOf,List.getElem?_map,formula j bound]
    split
    · rfl
    · rfl
  · have expandedBound : ¬j<(expand (input.length/16) (bytesOf input.val)).length := by omega
    simp only [List.getElem?_eq_none_iff.mpr expandedBound]
    simp only [bytesOf,List.getElem?_map,List.getElem?_eq_none_iff.mpr bound,Option.map_none]

#print axioms source_expansion
end AspisR1.PSem_Values
