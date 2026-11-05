import NGL_CloneDomain
set_option autoImplicit false
namespace NGL_BorrowFrame
open Aeneas.Std
/-- Natural addresses interpret one valid, non-wrapping Rust allocation.
The physical address interpretation remains part of the retained ABI boundary. -/
def contents (heap : Nat → U8) (pointer length : Nat) : List U8 :=
  (List.range length).map (fun offset => heap (pointer+offset))

theorem preserved (before after : Nat → U8) (pointer length : Nat)
    (frame : ∀ offset, offset < length → after (pointer+offset)=before (pointer+offset)) :
    contents after pointer length = contents before pointer length := by
  apply List.map_congr_left
  intro offset member
  exact frame offset (List.mem_range.mp member)

/-- Header identity and an old-allocation frame recover every returned byte;
no copy implementation or finite sampled offset is assumed. -/
theorem forwarded (before after : Nat → U8) (pointer length resultPointer resultLength : Nat)
    (samePointer : resultPointer=pointer) (sameLength : resultLength=length)
    (frame : ∀ offset, offset < length → after (pointer+offset)=before (pointer+offset)) :
    contents after resultPointer resultLength = contents before pointer length := by
  subst resultPointer
  subst resultLength
  exact preserved before after pointer length frame
#print axioms preserved
#print axioms forwarded
end NGL_BorrowFrame
