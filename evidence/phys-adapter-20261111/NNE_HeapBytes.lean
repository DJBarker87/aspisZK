import NNE_CopyFrame
import NNE_Entry
set_option autoImplicit false
noncomputable section
namespace NNE_HeapBytes
open Aeneas Aeneas.Std AspisR1 S2Trust S2W_D189Entry S2W_TrustedStd
open S2W_CommittedCheckpoint S2W_WrapperLaws S2W_ReturnedCheckpoint
/-- Account-data component only. Metadata and token correspondence are separate
proved components, never erased by claiming this to be the complete world. -/
def bytes (p : Payload) : List UInt8 :=
 (List.range p.descriptor.length).map p.contents
def Image (s : RSL.SdkState) (h : Heap (Nat → Record)) : Prop :=
 ∀ i, (s.cells i).payload = bytes (h.payload i)

theorem source_bytes (bs : List UInt8) : bytes (source bs) = bs := by
 apply List.ext_getElem
 · simp [bytes,source]
 · intro i hi hj
   simp [bytes,source,List.getElem?_eq_getElem hj]

theorem entry (e : Entry) (n : Nat) : Image (NNE_Entry.state e n) e.heap := by
 intro i
 change nativeBytes (e.buffers i) = bytes (e.payload i)
 simpa only [bytes,Entry.payload,nativeBytes,List.length_map,source] using
  (source_bytes (nativeBytes (e.buffers i))).symm

theorem copied_bytes (dst : Payload) (bs : List UInt8)
 (length : dst.descriptor.length = bs.length) :
 bytes (copied dst (source bs)) = bs := by
 apply List.ext_getElem
 · simp [bytes,copied,length]
 · intro i hi hj
   have bound : i < dst.descriptor.length := by simpa [bytes,copied] using hi
   simp [bytes,copied,source,bound,List.getElem?_eq_getElem hj]

/-- Extensional SAME-write transport at arbitrary cell/index, without reducing
or constructing a 1768-byte buffer. Inaccessible native contents remain framed
by TrustedStd.copyHeap, not projected away as an extra write. -/
theorem copy_image (s post : RSL.SdkState) (h : Heap (Nat → Record))
 (dst : Nat) (bs : List UInt8) (image : Image s h)
 (length : bs.length = (s.cells dst).payload.length)
 (write : ∀ i, (post.cells i).payload = if i = dst then bs else (s.cells i).payload) :
 Image post (copyHeap h dst (source bs)) := by
 intro i
 rw [write i]
 by_cases hi : i = dst
 · subst i
   simp only [if_true,copyHeap,S2Trust.put,if_true]
   apply (copied_bytes _ bs ?_).symm
   have hs := congrArg List.length (image dst)
   simp only [bytes,List.length_map,List.length_range] at hs
   exact hs.symm.trans length.symm
 · simp only [copyHeap,S2Trust.put,if_neg hi]
   exact image i

theorem bracket_image (e : Entry) (s post : RSL.SdkState) (dst : Nat) (bs : List UInt8)
 (image : Image s e.heap) (length : bs.length = (s.cells (e.handles dst).1).payload.length)
 (write : ∀ i, (post.cells i).payload =
  if i = (e.handles dst).1 then bs else (s.cells i).payload) :
 Image post (writeBracket e.heap dst 0 0 (source bs)) := by
 rw [write_bracket e.heap dst 0 0 (source bs) rfl rfl]
 exact copy_image s post e.heap (e.handles dst).1 bs image length write
#print axioms source_bytes
#print axioms entry
#print axioms copied_bytes
#print axioms copy_image
#print axioms bracket_image
end NNE_HeapBytes
end
