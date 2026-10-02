import AspisV8R19.R251PrivateAddSub

/-! Private R110 complex additive/scalar leaves, on canonical encodings.
No complex product/square/norm, Option input, coefficient, vector or inverse
execution claim is made here. -/
set_option autoImplicit false
namespace AspisV8R19.R252PrivateComplexLinear
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (B C)
open ComplexBaseExecution (encodeBase)
open R250PrivateBaseExecution (encodeC)
noncomputable section

theorem c_add (z w : CM31Exact) :
    C.add (encodeC z) (encodeC w) = .ok (encodeC (z+w)) := by
  simp [C.add,encodeC,R251PrivateAddSub.b_add_encode,
    QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,bind_tc_ok]

theorem c_sub (z w : CM31Exact) :
    C.sub (encodeC z) (encodeC w) = .ok (encodeC (z-w)) := by
  simp [C.sub,encodeC,R251PrivateAddSub.b_sub_encode,
    QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,bind_tc_ok]

theorem c_double (z : CM31Exact) :
    C.double (encodeC z) = .ok (encodeC (z+z)) := by
  simp only [C.double,c_add]

theorem c_half (z : CM31Exact) :
    C.half (encodeC z) = .ok (encodeC (z/2)) := by
  have h : C.half (encodeC z) = (do
      let m ← R240HalfExecution.rawCMHalf (R163ComplexExecution.encode z)
      ok (m.a,m.b)) := by
    rfl
  rw [h,R240HalfExecution.cm_half_exact]
  rfl

theorem c_mul_m (z : CM31Exact) (x : M31Exact) :
    C.mul_m (encodeC z) (encodeBase x) =
      .ok (encodeC (z*R240HalfExecution.mapBase x)) := by
  simp [C.mul_m,encodeC,R250PrivateBaseExecution.mul_encoded,
    R240HalfExecution.mapBase,QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul,bind_tc_ok]

theorem c_times_r (z : CM31Exact) :
    C.times_r (encodeC z) = .ok (encodeC (qm31R*z)) := by
  have he : (⟨z.re+z.re-z.im,z.re+(z.im+z.im)⟩ : CM31Exact)=qm31R*z := by
    apply QuadraticAlgebra.ext <;>
      simp [qm31R,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring
  calc
    C.times_r (encodeC z) =
        .ok (encodeC (⟨z.re+z.re-z.im,z.re+(z.im+z.im)⟩ : CM31Exact)) := by
      simp [C.times_r,encodeC,R251PrivateAddSub.b_add_encode,
        R251PrivateAddSub.b_sub_encode,bind_tc_ok]
    _ = .ok (encodeC (qm31R*z)) := by rw [he]

#print axioms c_add
#print axioms c_sub
#print axioms c_double
#print axioms c_half
#print axioms c_mul_m
#print axioms c_times_r
end
end AspisV8R19.R252PrivateComplexLinear
