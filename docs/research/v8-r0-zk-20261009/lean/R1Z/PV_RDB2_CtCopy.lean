import R1Z.PV_RDB2_DL_CtSelected
import R1Z.PV_RDB2_CopyEffects

namespace R1Z.PV_RDB2_CtCopy
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_CopyEffects

def start (side : PV_DL_CtFinal.Side) (n : Nat) (bytes : List U8) : Nat :=
  match side with
  | .Left => 0
  | .Right => bytes.length-n

theorem view (side : PV_DL_CtFinal.Side) (n : Nat) (bytes : List U8)
    (bound : n ≤ bytes.length) :
    (bytes.drop (start side n bytes)).take n = PV_DL_Truncation.value side n bytes := by
  cases side with
  | Left => rfl
  | Right =>
    simp only [start,PV_DL_Truncation.value]
    exact List.take_of_length_le (by simp only [List.length_drop]; omega)

theorem copy_complete (side : PV_DL_CtFinal.Side) (heap : Heap U8) (src dst n : Nat)
    (full : (heap src).length = 32) (output : (heap dst).length = n) (bound : n ≤ 32) :
    copyRange heap src (start side n (heap src)) dst =
      ok (write heap dst (PV_DL_Truncation.value side n (heap src))) := by
  have hb : start side n (heap src)+(heap dst).length ≤ (heap src).length := by
    cases side <;> simp only [start,output,full] <;> omega
  rw [range_complete heap src _ dst hb,output,view side n (heap src) (by omega)]

theorem returned_bytes (side : PV_DL_CtFinal.Side) (heap : Heap U8) (src dst n : Nat) :
    write heap dst (PV_DL_Truncation.value side n (heap src)) dst =
      PV_DL_Truncation.value side n (heap src) := if_pos rfl

theorem returned_length (side : PV_DL_CtFinal.Side) (heap : Heap U8) (src dst n : Nat)
    (bound : n ≤ (heap src).length) :
    (write heap dst (PV_DL_Truncation.value side n (heap src)) dst).length = n := by
  rw [returned_bytes]
  exact PV_DL_Truncation.length side n (heap src) bound

theorem complete_frame (side : PV_DL_CtFinal.Side) (heap : Heap U8) (src dst n location : Nat)
    (frame : location ≠ dst) :
    write heap dst (PV_DL_Truncation.value side n (heap src)) location = heap location :=
  if_neg frame

/-- Successful native subtraction computes the suffix start without a wrap. -/
theorem subtraction (n : Nat) (bound : n ≤ 32) : (32-n)+n=32 := by omega

#print axioms view
#print axioms copy_complete
#print axioms returned_bytes
#print axioms returned_length
#print axioms complete_frame
#print axioms subtraction
#print axioms PV_DL_CtCarrier.complete
#print axioms PV_DL_CtSelected.selected_native
end R1Z.PV_RDB2_CtCopy
