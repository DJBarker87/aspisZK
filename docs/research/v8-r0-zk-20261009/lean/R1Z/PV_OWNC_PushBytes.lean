import R1Z.PV_OWNC_Vector
set_option autoImplicit false
namespace R1Z.PV_OWNC_PushBytes
open PV_OWNC_Vector PV_OWN_Heap PV_OWN_Bytes PV_OWN_View
/-- Vec::push writes the item before publishing the increased initialized len.
Only active representation bytes are required from a source typed store. -/
theorem initialized {T : Type} (k : Codec T) (b : Buffer T) (v : T) (actual : Bytes)
 (h:Valid k b) (room:b.length<b.capacity)
 (bounded:∀ i x, k.encode v i=some x → i<k.width)
 (bytes:PV_OWNB_Padding.Agrees (k.encode v) actual) :
 View k (push k b v actual).cell (b.length*k.width) v := by
 apply PV_OWNB_PaddingStore.written (k.encode v) actual k.width b.cell _ _ bounded bytes
 unfold Valid at h
 unfold Fits
 rw [h.2.1]
 have eq:b.length*k.width+k.width=(b.length+1)*k.width := by
  simp only [Nat.add_mul,Nat.one_mul]
 rw [eq]
 exact Nat.mul_le_mul_right k.width (by omega)

theorem prefix {T : Type} (k : Codec T) (b : Buffer T) (v : T) (actual : Bytes)
 (h:Valid k b) (bounded:∀ x i z, k.encode x i=some z → i<k.width)
 (i : Nat) (hi:i<b.length) :
 View k (push k b v actual).cell (i*k.width) (b.values i) := by
 unfold Valid at h
 apply PV_OWNB_RegionFrame.disjoint (k.encode (b.values i)) actual b.cell
  (i*k.width) k.width (b.length*k.width) k.width (h.2.2.2.2 i hi) (bounded _)
 left
 calc
  i*k.width+k.width=(i+1)*k.width := by simp only [Nat.add_mul,Nat.one_mul]
  _≤b.length*k.width := Nat.mul_le_mul_right k.width (by omega)
#print axioms initialized
#print axioms prefix
end R1Z.PV_OWNC_PushBytes
