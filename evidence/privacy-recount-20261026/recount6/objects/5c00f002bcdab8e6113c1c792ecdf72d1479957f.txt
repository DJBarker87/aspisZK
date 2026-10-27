import R1Z.PV_CBL_PadSuffixValue
import R1Z.PV_CBL_ArrayPrefix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadSuffixBytes
set_option autoImplicit false
theorem byte (out : Array U8 64#usize) (suffix : Array U8 8#usize) (j : Nat) (hj : j<64) :
    (PV_CBL_PadSuffixValue.value out suffix).val[j]! =
      if j<56 then out.val[j]! else suffix.val[j-56]! := by
  unfold PV_CBL_PadSuffixValue.value
  rw [PV_CBL_ArrayPrefix.set_get _ 63#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 62#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 61#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 60#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 59#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 58#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 57#usize _ j (by decide)]
  rw [PV_CBL_ArrayPrefix.set_get _ 56#usize _ j (by decide)]
  change (if j=63 then suffix.val[7]! else (if j=62 then suffix.val[6]! else (if j=61 then suffix.val[5]! else (if j=60 then suffix.val[4]! else (if j=59 then suffix.val[3]! else (if j=58 then suffix.val[2]! else (if j=57 then suffix.val[1]! else (if j=56 then suffix.val[0]! else out.val[j]!)))))))) = if j<56 then out.val[j]! else suffix.val[j-56]!
  by_cases h : j<56
  · simp only [if_pos h,if_neg (show j≠63 by omega),if_neg (show j≠62 by omega),
      if_neg (show j≠61 by omega),if_neg (show j≠60 by omega),if_neg (show j≠59 by omega),
      if_neg (show j≠58 by omega),if_neg (show j≠57 by omega),if_neg (show j≠56 by omega)]
  · have cases : j=56 ∨ j=57 ∨ j=58 ∨ j=59 ∨ j=60 ∨ j=61 ∨ j=62 ∨ j=63 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
#print axioms byte
end R1Z.PV_CBL_PadSuffixBytes
