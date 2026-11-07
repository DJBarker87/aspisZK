import LIB_Carriers
set_option autoImplicit false
namespace LIBC_Bytes
open Aeneas Aeneas.Std
noncomputable def raw (b : RSL.Bytes) : Slice U8 :=
 if h : b.length ≤ Usize.max then
  ⟨LIB_Carriers.rawBytes b,by simpa only [NNC_ByteCarriers.nativeList,List.length_map] using h⟩
 else ⟨[],by simp⟩
theorem raw_val (b : RSL.Bytes) (h : b.length ≤ Usize.max) :
 (raw b).val = LIB_Carriers.rawBytes b := by simp only [raw,dif_pos h]
theorem raw_length (b : RSL.Bytes) (h : b.length ≤ Usize.max) :
 (raw b).val.length = b.length := by rw [raw_val b h];rfl
 theorem from_native (s : Slice U8) : raw (LIB_Carriers.bytes s) = s := by
 have bound : (LIB_Carriers.bytes s).length ≤ Usize.max := by
  change (s.val.map _).length ≤ Usize.max
  simpa only [List.length_map] using s.property
 apply Subtype.ext
 rw [raw_val _ bound,LIB_Carriers.bytes_roundtrip]
theorem to_native (b : RSL.Bytes) (h : b.length ≤ Usize.max) :
 LIB_Carriers.bytes (raw b) = b := by
 change NNC_ByteCarriers.host (raw b).val = b
 rw [raw_val b h]
 exact LIB_Carriers.byte_roundtrip b
#print axioms raw_val
#print axioms raw_length
#print axioms from_native
#print axioms to_native
end LIBC_Bytes
