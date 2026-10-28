import R1Z.PV_RDB2_LayoutGuards

namespace R1Z.PV_RDB2_LayoutRepeat
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_LayoutGuards

def full (align stride : Nat) (bytes : Option Nat) : Except Unit (Layout × Nat) :=
  match bytes with
  | none => .error ()
  | some bytes => .ok (⟨bytes,align⟩,stride)

theorem padded_complete (limit size count align : Nat) :
    full align size (PV_RDB2_Layout.historical limit size count) =
      full align size (PV_RDB2_Layout.deployed limit size count) := by
  rw [PV_RDB2_Layout.same_result]

theorem padded_effect {World : Type} (limit size count align : Nat) (world : World) :
    (ok (full align size (PV_RDB2_Layout.historical limit size count),world) :
      Result (Except Unit (Layout × Nat) × World)) =
      ok (full align size (PV_RDB2_Layout.deployed limit size count),world) := by
  rw [padded_complete]

/-- The product word check and subsequent Layout check collapse to the
Layout bound because the latter is below the word maximum. No wrapping
product is used as the size of a successful allocation. -/
theorem checked_mul_layout (wordLimit layoutLimit size count : Nat)
    (limits : layoutLimit ≤ wordLimit) :
    (if size*count ≤ wordLimit then
      PV_RDB2_Layout.checked layoutLimit (size*count) else none) =
      PV_RDB2_Layout.checked layoutLimit (size*count) := by
  by_cases h : size*count ≤ layoutLimit
  · have hw : size*count ≤ wordLimit := by omega
    simp only [hw,if_true]
  · by_cases hw : size*count ≤ wordLimit
    · simp only [hw,if_true]
    · simp only [hw,if_false,PV_RDB2_Layout.checked,h,if_false]

def arrayResult (result : Except Unit (Layout × Nat)) : Except Unit Layout :=
  match result with
  | .error _ => .error ()
  | .ok (layout,_) => .ok layout

theorem layout_array (halfWord size count align : Nat) :
    arrayResult (full align size
      (PV_RDB2_Layout.historical (maximum halfWord align) size count)) =
      arrayResult (full align size
        (PV_RDB2_Layout.deployed (maximum halfWord align) size count)) := by
  rw [padded_complete]

#print axioms padded_complete
#print axioms padded_effect
#print axioms checked_mul_layout
#print axioms layout_array
end R1Z.PV_RDB2_LayoutRepeat
