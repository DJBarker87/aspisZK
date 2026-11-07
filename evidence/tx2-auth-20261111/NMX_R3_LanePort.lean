import NMX_R3_LaneTotal
set_option autoImplicit false
namespace NMX_R3_LanePort
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_LaneCarrier

def fromByte (b : UInt8) : U8 := UScalar.ofNatCore b.toNat (UInt8.toNat_lt b)

theorem byte_roundtrip (b : UInt8) : byte (fromByte b) = b := by
 simp only [byte, fromByte, UScalar.ofNatCore_val_eq, UInt8.ofNat_toNat]

def input (b : Bytes) (extent : b.length = 768) : Slice U8 :=
 ⟨b.map fromByte,by rw [List.length_map, extent]; scalar_tac⟩

theorem input_image (b : Bytes) (extent : b.length = 768) :
 (input b extent).val.map byte = b := by
 simp only [input, List.map_map, Function.comp_def, byte_roundtrip]
 have identity (xs : Bytes) : xs.map (fun x => x) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x) ih
 exact identity b

/-- The first length test runs before an input buffer is materialized. Only its
768-byte continuation needs a Rust slice. Raw all-length equality is LaneTotal. -/
def pureResult (b : Bytes) : Option LaneState :=
 if extent : b.length = 768 then
  match NCV_Reference.decode_lane_ref (input b extent) with
  | .ok r => result r
  | .fail _ => none
  | .div => none
 else none

theorem pure_eq (b : Bytes) : pureResult b = TX2_217.laneDecode b := by
 unfold pureResult
 split
 · rename_i extent
   obtain ⟨r,call,mapped⟩ := NMX_R3_LaneTotal.value (input b extent)
   rw [call]
   simpa only [input_image] using mapped
 · rename_i wrong
   have bad : TX2_217.headerBad b = true := by
    simp only [TX2_217.headerBad,
     show (b.length != LANE_ACCOUNT_BYTES)=true by simp only [LANE_ACCOUNT_BYTES,bne_iff_ne]; exact wrong,
     Bool.true_or]
   simp only [TX2_217.laneDecode,bad,↓reduceIte]
#print axioms byte_roundtrip
#print axioms input_image
#print axioms pure_eq
end NMX_R3_LanePort
