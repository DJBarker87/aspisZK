import NBU_SourceWindows
set_option autoImplicit false
namespace NBU_AnyWindow
open Aeneas Aeneas.Std
/-- Arbitrary-width slice copies, including the 1520-byte late and 216-byte
payment windows. Bounds remain explicit caller obligations. -/
theorem source {n m : Usize} (out : Array U8 n) (bytes : Array U8 m)
    (start j : Nat) (room : start+m.val ≤ n.val) (index : j < n.val) :
    (out.setSlice! start bytes.val).val[j]! =
      NBU_CopyWindows.window (fun i => out.val[i]!) (fun i => bytes.val[i]!) start m.val j := by
  rw [NBU_CopyWindows.window_spec]
  by_cases inside : start ≤ j ∧ j < start+m.val
  · rw [if_pos inside]
    have mid := Array.setSlice!_getElem!_middle out bytes.val start j
      (by have bs := bytes.property; scalar_tac)
    simpa only [Array.getElem!_Nat_eq] using mid
  · rw [if_neg inside]
    by_cases early : j < start
    · have pre := Array.setSlice!_getElem!_prefix out bytes.val start j early
      simpa only [Array.getElem!_Nat_eq] using pre
    · have post := Array.setSlice!_getElem!_suffix out bytes.val start j
        (by have bs := bytes.property; scalar_tac)
      simpa only [Array.getElem!_Nat_eq] using post
#print axioms source
end NBU_AnyWindow
