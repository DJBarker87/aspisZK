import NNH_MAccountCarrier
import NNC_ByteCarriers
set_option autoImplicit false
noncomputable section
namespace NNH_ModelCarrier
open NND_Carrier NNH_ModelCarrier
open Aeneas Aeneas.Std

theorem bytes_host (b : Slice U8) : bytes b = NNC_ByteCarriers.host b.val := rfl

def fromBytes (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) : Slice U8 :=
 ⟨NNC_ByteCarriers.nativeList bs,by simpa [NNC_ByteCarriers.nativeList] using h⟩

theorem from_bytes (b : Slice U8) (h : (bytes b).length ≤ Usize.max) : fromBytes (bytes b) h = b := by
 apply Subtype.ext
 exact NNC_ByteCarriers.native_host b.val

theorem bytes_from (bs : RSL.Bytes) (h : bs.length ≤ Usize.max) : bytes (fromBytes bs h) = bs :=
 NNC_ByteCarriers.host_native bs

theorem bytes_bound (b : Slice U8) : (bytes b).length ≤ Usize.max := by
 rw [bytes_length]
 exact b.property

#print axioms bytes_host
#print axioms from_bytes
#print axioms bytes_from
#print axioms bytes_bound
end NNH_ModelCarrier
end
