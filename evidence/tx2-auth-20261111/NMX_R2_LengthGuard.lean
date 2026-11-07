import NMX_R2_Carrier
set_option autoImplicit false
namespace NMX_R2_LengthGuard
open Aeneas Aeneas.Std
theorem literal : (7#usize).val = 7 := by scalar_tac
#print axioms literal

theorem value {A : Type} (a : Slice A) : (Slice.len a).val = a.val.length := by
 simp [Slice.len]

theorem equal {A : Type} (a : Slice A) : Slice.len a = 7#usize ↔ a.val.length = 7 := by
 constructor
 · intro same
   have h := congrArg (fun v : Usize => v.val) same
   simpa only [value,literal] using h
 · intro same
   apply UScalar.eq_of_val_eq
   simpa only [value,literal] using same

theorem less {A : Type} (a : Slice A) : (Slice.len a < 7#usize) ↔ a.val.length < 7 := by
 change (Slice.len a).val < 7 ↔ a.val.length < 7
 rw [value]
#print axioms value
#print axioms equal
#print axioms less
end NMX_R2_LengthGuard
