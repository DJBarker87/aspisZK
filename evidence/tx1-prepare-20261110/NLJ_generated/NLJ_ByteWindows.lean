import NLC_CopyFrames
set_option autoImplicit false
namespace AspisR1.NLJ_ByteWindows
open Aeneas Aeneas.Std
/-- Complete byte identity from arbitrary direct-index observations, never
from an address test. Includes the empty and out-of-range partitions. -/
theorem list_windows {A : Type} (actual source : List A)
 (length : actual.length = source.length)
 (cells : ∀ i, i < source.length → actual[i]? = source[i]?) : actual = source := by
 apply List.ext_getElem?
 intro i
 by_cases inside : i < source.length
 · exact cells i inside
 · have ha : actual[i]? = none := by simp only [List.getElem?_eq_none_iff];omega
   have hs : source[i]? = none := by simp only [List.getElem?_eq_none_iff];omega
   rw [ha,hs]
/-- KMX value/frame composition is reused unchanged; no copy loop is unfolded. -/
theorem copy_window {A : Type} (source target : Nat → A) (start count i : Nat)
 (inside : start ≤ i ∧ i < start+count) :
 KMX_CopyMeaning.loop source target start count i = source i :=
 NLC_CopyFrames.copied_window source target start count i inside
#print axioms list_windows
#print axioms copy_window
end AspisR1.NLJ_ByteWindows
