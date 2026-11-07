import PCF_AccountRef.Funs
import PCF_Count
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_CountWord

def tag : PCF_Count.Reply → U8
  | .ok => 0#u8 | .notEnoughKeys => 1#u8 | .invalidArgument => 2#u8

theorem result (count expected : Usize) :
    PCF_AccountRef.count_reference count expected =
      ok (tag (PCF_Count.source count.val expected.val)) := by
  by_cases he : count = expected
  · subst expected
    simp [PCF_AccountRef.count_reference, PCF_Count.source, tag]
  · have hv : count.val ≠ expected.val := fun h => he (UScalar.eq_of_val_eq h)
    by_cases hl : count.val < expected.val
    · simp [PCF_AccountRef.count_reference, PCF_Count.source, tag, he, hv, hl]
    · simp [PCF_AccountRef.count_reference, PCF_Count.source, tag, he, hv, hl]

#print axioms result
end PCF_CountWord
