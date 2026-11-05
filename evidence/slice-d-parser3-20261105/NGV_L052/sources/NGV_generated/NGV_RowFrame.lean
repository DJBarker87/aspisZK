import NGV_RowPayload
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_RowFrame
open NGV_RowPayload NGV_ByteWindow
/-- Spatial composition of the two original writes. Both the untouched prefix
and every later output window belong to the SAME arbitrary output buffer. -/
theorem outside (input before : Slice U8) (r : Nat) (live : r<27)
 (inputSize : input.val.length=7015) (packet : Packet input before r)
 (j : Nat) (frame : j<NGD_SemanticSchedule.dst r ∨
   NGD_SemanticSchedule.dst r+5+NFU_PacketDomains.payloadSize r≤j) :
 (after packet).val[j]?=before.val[j]? := by
 have fit : NGD_SemanticSchedule.src r+5 ≤ input.val.length := by
   have h:=(NGD_SemanticSchedule.windows r live).1;omega
 have headerSize:=select_length input (NGD_SemanticSchedule.src r) 5 fit
 simp only [after,middle,write,Slice.setSlice!_val]
 rw [List.setSlice!_getElem?_same _ packet.value.val (NGD_SemanticSchedule.dst r+5) j (by
   rw [packet.size];rcases frame with low|high
   · left;omega
   · exact Or.inr high)]
 exact List.setSlice!_getElem?_same _ _ (NGD_SemanticSchedule.dst r) j (by
   rw [headerSize];rcases frame with low|high
   · exact Or.inl low
   · right;omega)
theorem later (input before : Slice U8) (r later j : Nat) (live : r<27)
 (inputSize : input.val.length=7015) (packet : Packet input before r)
 (order : r<later) (bound : later<27) (position : NGD_SemanticSchedule.dst later≤j) :
 (after packet).val[j]?=before.val[j]? := by
 apply outside input before r live inputSize packet j
 exact Or.inr (le_trans (NGD_SemanticSchedule.disjoint r later order bound) position)
#print axioms outside
#print axioms later
end NGV_RowFrame
