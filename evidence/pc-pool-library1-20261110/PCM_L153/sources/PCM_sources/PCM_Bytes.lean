import NNC_ByteCarriers
import RSL_Base
set_option autoImplicit false
namespace PCM_Bytes
open Aeneas Aeneas.Std

def bytes (b : Slice U8) : RSL.Bytes := NNC_ByteCarriers.host b.val
abbrev rawBytes := NNC_ByteCarriers.nativeList

def fromBytes (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) : Slice U8 :=
  ⟨rawBytes bs,by simpa [NNC_ByteCarriers.nativeList] using h⟩

theorem from_bytes (b : Slice U8) (h : (bytes b).length ≤ Usize.max) :
    fromBytes (bytes b) h = b := by
  apply Subtype.ext
  exact NNC_ByteCarriers.native_host b.val

theorem bytes_from (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) :
    bytes (fromBytes bs h) = bs := NNC_ByteCarriers.host_native bs

theorem bytes_bound (b : Slice U8) : (bytes b).length ≤ Usize.max := by
  simpa [bytes,NNC_ByteCarriers.host] using b.property

#print axioms from_bytes
#print axioms bytes_from
#print axioms bytes_bound
end PCM_Bytes
