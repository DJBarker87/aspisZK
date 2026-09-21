import Mathlib.Algebra.Ring.Basic

/-! Exact algebra for complementary tensor children. This is a logical
tensor-tree equivalence over a ring, not extracted QM31 arithmetic or the
in-place Rust array loop, and not a privacy statement. -/
set_option autoImplicit false
namespace AspisV8R17.TensorComplement
variable {R : Type*} [Ring R]

theorem split (p z : R) :
    (p - p*z, p*z) = (p*(1-z), p*z) := by
  rw [mul_sub, mul_one]

def reference (scale : R) : List R → List R
  | [] => [scale]
  | z :: zs => reference (scale*(1-z)) zs ++ reference (scale*z) zs

def shared (scale : R) : List R → List R
  | [] => [scale]
  | z :: zs => shared (scale-scale*z) zs ++ shared (scale*z) zs

/-- Arbitrary length, scale, and coordinates; no nonzero challenge premise. -/
theorem tensor_eq (point : List R) (scale : R) :
    shared scale point = reference scale point := by
  induction point generalizing scale with
  | nil => rfl
  | cons z zs ih => simp only [shared, reference, ih, mul_sub, mul_one]

#print axioms split
#print axioms tensor_eq
end AspisV8R17.TensorComplement
