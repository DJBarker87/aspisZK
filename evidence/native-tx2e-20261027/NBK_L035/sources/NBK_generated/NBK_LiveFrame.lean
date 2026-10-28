import NBK_LiveBytes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBK_LiveFrame

def arr (s : Slice U8) (size : s.length = 800) : Array U8 800#usize := ⟨s.val,size⟩

/-- Full native observation law for the SAME 32-byte store, including frame. -/
theorem byte (out : Slice U8) (size : out.length = 800)
    (bytes : Array U8 32#usize) (level j : Nat)
    (row : level < 20) (index : j < 800) :
    (out.setSlice! (160+32*level) bytes.val).val[j]! =
      if j ≥ 160+32*level ∧ j < 192+32*level
      then bytes.val[j-(160+32*level)]! else out.val[j]! := by
  change (arr out size |>.setSlice! (160+32*level) bytes.val).val[j]! = _
  by_cases inside : j ≥ 160+32*level ∧ j < 192+32*level
  · rw [if_pos inside]
    have mid := Array.setSlice!_getElem!_middle (arr out size) bytes.val (160+32*level) j
      (by have := bytes.property; simp only [arr,Array.length]; omega)
    simpa only [Array.getElem!_Nat_eq] using mid
  · rw [if_neg inside]
    by_cases early : j < 160+32*level
    · have pre := Array.setSlice!_getElem!_prefix (arr out size) bytes.val (160+32*level) j early
      simpa only [Array.getElem!_Nat_eq,arr] using pre
    · have post := Array.setSlice!_getElem!_suffix (arr out size) bytes.val (160+32*level) j
        (by have := bytes.property; simp only [arr,Array.length]; omega)
      simpa only [Array.getElem!_Nat_eq,arr] using post

#print axioms byte
end NBK_LiveFrame
