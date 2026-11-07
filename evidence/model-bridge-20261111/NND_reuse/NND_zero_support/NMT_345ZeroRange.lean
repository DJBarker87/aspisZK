import NMT_345Checkpoint
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Numeric domain discharged from the ACTUAL slice bound, without a 4096
parent precondition or a concrete buffer evaluation. -/
theorem zero_increment (bytes : Slice U8) (i : Usize) (inside : i.val < bytes.val.length) :
 (Usize.wrapping_add i 1#usize).val = i.val + 1 := by
 rw [Usize.wrapping_add_val_eq]
 apply Nat.mod_eq_of_lt
 have bounded := bytes.property
 have capacity : Usize.max < UScalar.size .Usize := by
  rw [UScalar.size_def]
  scalar_tac
 change i.val + 1 < UScalar.size .Usize
 omega
#print axioms zero_increment
end NMT_345
