import XSe_ChunkList
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunkAt
/-- Nominal slices retain the exact SAME standard chunk bytes at each index. -/
theorem source (s : Slice U8) (i : Nat) (bound : i<(XSe_ChunkList.slices s).length)
 (fallback : Slice U8) :
 ((XSe_ChunkList.slices s)[i]?.getD fallback).val=(s.val.drop (32*i)).take 32 := by
 have hb : i<(List.toChunksExact 32 (by decide) s.val).1.length := by
  simpa only [XSe_ChunkList.slices,List.length_map,List.length_attach] using bound
 rw [List.getElem?_eq_getElem bound,Option.getD_some]
 have get : ((XSe_ChunkList.slices s)[i]'bound).val=
  (List.toChunksExact 32 (by decide) s.val).1[i] := by
  simp only [XSe_ChunkList.slices,List.getElem_map,List.getElem_attach]
 rw [get]
 exact XSe_ChunksWindow.source s.val i _ (List.getElem?_eq_getElem hb)
#print axioms source
end XSe_ChunkAt
