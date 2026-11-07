import NCV_ZeroStep
import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_ByteIndex
open Aeneas Aeneas.Std NMX_R3_ByteCarrier

theorem mapped (xs : List U8) (i : Nat) :
 (xs.map byte).getD i 0 = byte ((xs[i]?).getD 0#u8) := by
 induction xs generalizing i with
 | nil => cases i <;> rfl
 | cons x xs ih =>
   cases i with
   | zero => rfl
   | succ i => exact ih i

/-- Exact same original byte at any in-window coordinate, even when the
original list itself is short; default-zero behavior agrees too. -/
theorem window (b : Slice U8) (s n i : Nat) (index : i < n) :
 (RSL.slice (b.val.map byte) s (s+n)).getD i 0 =
 byte (NCV_ZeroStep.byte b (s+i)) := by
 have width : s+n-s=n := by omega
 rw [NMX_R3_ByteCarrier.window, width, mapped]
 unfold NCV_ZeroStep.byte
 congr 1
 simp [List.getElem?_take, List.getElem?_drop, index]
#print axioms mapped
#print axioms window
end NMX_R3_ByteIndex
