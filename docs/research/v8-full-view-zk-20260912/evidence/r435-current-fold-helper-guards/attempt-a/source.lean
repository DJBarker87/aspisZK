import AspisV8R19.R195CountedSliceFoldArithmetic
import AspisV8R19.R432PointerPrimitive

/-! Scalar guard for native helper115's captured usize-to-u64 casts,
AddChecked and overflow-field read, expressed using the Aeneas scalar library.
The explicit helper fragment keeps its rejected-guard continuation arbitrary:
no panic/formatting/abort semantics is invented. The pointer-order theorem is
within R432 storage representation. Neither theorem is a full Rust memory or
native helper execution correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.R435HelperGuards
open Aeneas Aeneas.Std Result

def helper115Overflow (lhs rhs : Usize) : Bool :=
  (UScalar.overflowing_add (UScalar.cast .U64 lhs) (UScalar.cast .U64 rhs)).2

def helper115Fragment (rejected : Result Unit) (lhs rhs : Usize) : Result Unit :=
  if helper115Overflow lhs rhs then rejected else .ok ()

theorem cast_usize_u64_value (x : Usize) :
    (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h := x.hBounds
  simpa [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq,
    UScalarTy.numBits] using h

theorem helper115_no_overflow (i len : Usize) (hi : i.val < len.val) :
    helper115Overflow i (1#usize) = false := by
  have hbound := R195CountedSliceFoldArithmetic.successor_bound i len hi
  simp only [UScalarTy.Usize_numBits_eq] at hbound
  have hs := UScalar.overflowing_add_eq
    (UScalar.cast .U64 i) (UScalar.cast .U64 (1#usize))
  have hnot : ¬ ((UScalar.cast .U64 i).val +
      (UScalar.cast .U64 (1#usize)).val > UScalar.max .U64) := by
    rw [cast_usize_u64_value, cast_usize_u64_value]
    simp only [UScalar.max, UScalar.size, UScalarTy.numBits] at *
    omega
  rw [if_neg hnot] at hs
  exact hs.2

theorem helper115_success (rejected : Result Unit) (i len : Usize)
    (hi : i.val < len.val) :
    helper115Fragment rejected i (1#usize) = .ok () := by
  simp only [helper115Fragment, helper115_no_overflow i len hi, Bool.false_eq_true,
    if_false]

theorem helper114_backed_order {T : Type} (id : Nat)
    (a : R432PointerPrimitive.Allocation T) (start length : Nat) :
    (R432PointerPrimitive.backedPointer id a (start + length)).address ≥
      (R432PointerPrimitive.backedPointer id a start).address := by
  simp only [R432PointerPrimitive.backedPointer]
  omega

#print axioms cast_usize_u64_value
#print axioms helper115_no_overflow
#print axioms helper115_success
#print axioms helper114_backed_order
end AspisV8R19.R435HelperGuards
