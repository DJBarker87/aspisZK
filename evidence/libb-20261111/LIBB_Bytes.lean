import LIB_Carriers
set_option autoImplicit false
namespace LIBB_Bytes
open Aeneas Aeneas.Std
abbrev bytes := LIB_Carriers.bytes
def fromBytes (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) : Slice U8 :=
  ⟨LIB_Carriers.rawBytes bs, by simpa [NNC_ByteCarriers.nativeList] using h⟩
theorem from_bytes (b : Slice U8) (h : (bytes b).length ≤ Usize.max) :
    fromBytes (bytes b) h = b := by
  apply Subtype.ext
  exact LIB_Carriers.bytes_roundtrip b
theorem bytes_from (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) :
    bytes (fromBytes bs h) = bs := NNC_ByteCarriers.host_native bs
theorem bytes_bound (b : Slice U8) : (bytes b).length ≤ Usize.max := by
  rw [NMS_R2N_RSLScalars.bytes_length]
  exact b.property
#print axioms from_bytes
#print axioms bytes_from
#print axioms bytes_bound
end LIBB_Bytes
