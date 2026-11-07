import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_Scalar
open Aeneas Aeneas.Std

theorem usize_compare (a b : Usize) : (a.val != b.val) = (a != b) := by
 simp [bne,Aeneas.Std.instBEqUScalar_1]
 constructor
 · intro h; exact UScalar.eq_of_val_eq h
 · intro h; subst b; rfl

theorem slice_wrong_length (bytes : Slice U8) (length : bytes.val.length ≠ 1880) :
 (Slice.len bytes != 1880#usize) = true := by
 rw [← usize_compare]
 change (bytes.val.length != 1880) = true
 simp [length]
#print axioms usize_compare
#print axioms slice_wrong_length
end NMT_R2_Scalar
