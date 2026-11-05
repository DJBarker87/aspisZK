import NGV_RowFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_RowValues
open NGV_RowPayload NGV_ByteWindow
theorem header (input before : Slice U8) (r j : Nat) (live : r<27) (within : j<5)
 (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
 (packet : Packet input before r) :
 (after packet).val[NGD_SemanticSchedule.dst r+j]?=input.val[NGD_SemanticSchedule.src r+j]? := by
 have bounds:=NGD_SemanticSchedule.windows r live
 have sourceSize:=select_length input (NGD_SemanticSchedule.src r) 5 (by omega)
 simp only [after,middle,write,Slice.setSlice!_val]
 rw [List.setSlice!_getElem?_prefix _ _ (NGD_SemanticSchedule.dst r+5) _ (by omega)]
 rw [List.setSlice!_getElem?_middle _ _ (NGD_SemanticSchedule.dst r) _ (by
   rw [sourceSize];constructor
   · omega
   · constructor <;> omega)]
 simp [select,within]
theorem payload (input before : Slice U8) (r j : Nat) (live : r<27)
 (within : j<NFU_PacketDomains.payloadSize r)
 (outputSize : before.val.length=13831) (packet : Packet input before r) :
 (after packet).val[NGD_SemanticSchedule.dst r+5+j]?=packet.value.val[j]? := by
 have bounds:=NGD_SemanticSchedule.windows r live
 have middleSize : (middle input before r).val.length=13831 := by
   unfold middle;rw [write_length,outputSize]
 simp only [after,write,Slice.setSlice!_val]
 rw [List.setSlice!_getElem?_middle _ _ (NGD_SemanticSchedule.dst r+5) _ (by
   rw [packet.size];constructor
   · omega
   · constructor <;> omega)]
 congr 1
 omega
#print axioms header
#print axioms payload
end NGV_RowValues
