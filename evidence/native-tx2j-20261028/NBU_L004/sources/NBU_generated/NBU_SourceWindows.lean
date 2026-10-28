import NBU_CopyWindows
import NBK_LiveFrame
import NBK_SliceStore
set_option autoImplicit false
namespace NBU_SourceWindows
open Aeneas Aeneas.Std Result
/-- The emitted array store has precisely the KMX loop's value observation,
for an arbitrary offset, source bytes, destination and observed index. -/
theorem array_window {n : Usize} (out : Array U8 n) (bytes : Array U8 32#usize)
    (start j : Nat) (room : start+32 ≤ n.val) (index : j < n.val) :
    (out.setSlice! start bytes.val).val[j]! =
      NBU_CopyWindows.window (fun i => out.val[i]!) (fun i => bytes.val[i]!) start 32 j := by
  rw [NBU_CopyWindows.window_spec]
  by_cases inside : start ≤ j ∧ j < start+32
  · rw [if_pos inside]
    have mid := Array.setSlice!_getElem!_middle out bytes.val start j
      (by have bs : bytes.val.length = 32 := bytes.property; scalar_tac)
    simpa only [Array.getElem!_Nat_eq] using mid
  · rw [if_neg inside]
    by_cases early : j < start
    · have pre := Array.setSlice!_getElem!_prefix out bytes.val start j early
      simpa only [Array.getElem!_Nat_eq] using pre
    · have post := Array.setSlice!_getElem!_suffix out bytes.val start j
        (by have bs : bytes.val.length = 32 := bytes.property; scalar_tac)
      simpa only [Array.getElem!_Nat_eq] using post

/-- The whole live frontier source step is in the 800-byte native domain. -/
theorem live_row (out : Slice U8) (size : out.length = 800)
    (bytes : Array U8 32#usize) (k j : Nat) (row : k < 20) (index : j < 800) :
    (out.setSlice! (160+32*k) bytes.val).val[j]! =
      NBU_CopyWindows.window (fun i => out.val[i]!) (fun i => bytes.val[i]!) (160+32*k) 32 j := by
  rw [NBK_LiveFrame.byte out size bytes k j row index, NBU_CopyWindows.window_spec]
  rfl

#print axioms array_window
#print axioms live_row
end NBU_SourceWindows
