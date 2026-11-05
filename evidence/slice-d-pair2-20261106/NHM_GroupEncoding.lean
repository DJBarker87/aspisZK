import NHM_EEncoding
import NHI_GroupExtracted
set_option autoImplicit false
namespace NHM_GroupEncoding
open Aeneas Aeneas.Std Result AspisR1

/-- Exact complete-Result association to the retained compiled group update
reference, including invalid-index failure outside the native packet domain. -/
theorem reference (cells : Array FIo_Install.NE 12#usize) (group : Usize) (value : FIo_Install.NE) :
 FIo_FieldBridge.map NHM_EEncoding.encode (Array.update cells group value)=
 NHE_GroupRef.group_ref (NHM_EEncoding.encode cells) group (NGM_RawWords.nativeWords value) := by
 unfold NHE_GroupRef.group_ref
 cases h : cells.val[group.val]? with
 | none=>
  simp [Array.update,Array.getElem?_Usize_eq,NHM_EEncoding.encode,h,FIo_FieldBridge.map]
 | some x=>
  simp only [Array.update,Array.getElem?_Usize_eq,NHM_EEncoding.encode,List.getElem?_map,h,Option.map_some,FIo_FieldBridge.map,bind_tc_ok]
  congr 1
  apply Subtype.ext
  exact List.map_set

#print axioms reference
end NHM_GroupEncoding
