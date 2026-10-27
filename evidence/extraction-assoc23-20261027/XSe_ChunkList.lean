import XSe_ChunksWindow
import XSe_ChunkStage
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ChunkList
/-- Standard chunk bytes, with retained slice validity from the original input. -/
def slices (s : Slice U8) : List (Slice U8) :=
 (List.toChunksExact 32 (by decide) s.val).1.attach.map fun c =>
  ⟨c.val,by
   have h := List.toChunksExact_chunk_length (by decide : 0<32) s.val c.val c.property
   scalar_tac⟩
theorem count (s : Slice U8) : (slices s).length=s.val.length/32 := by
 simp only [slices,List.length_map,List.length_attach,XSe_ChunksCount.source]
theorem exact_size (bs : List U8) (c : List U8)
 (hc : c∈(List.toChunksExact 32 (by decide) bs).1) : c.length=32 := by
 rw [List.toChunksExact] at hc
 split at hc
 · simp only [List.not_mem_nil] at hc
 · simp only [List.mem_cons] at hc
   rcases hc with rfl | hc
   · simp only [List.length_take]; omega
   · exact exact_size (bs.drop 32) c hc
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

theorem size (s : Slice U8) (c : Slice U8) (member : c∈slices s) : c.val.length=32 := by
 unfold slices at member
 obtain ⟨entry,hentry,eq⟩ := List.mem_map.mp member
 subst c
 exact exact_size s.val entry.val entry.property
#print axioms count
#print axioms exact_size
#print axioms size
end XSe_ChunkList
