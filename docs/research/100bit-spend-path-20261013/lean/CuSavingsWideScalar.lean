import CuSavingsWideSquare
import CuSavingsWideMixed
set_option autoImplicit false
namespace AspisR1.CuSavingsWideArithmetic
open Aeneas Aeneas.Std Result AspisR1WideArithmetic

theorem scalar (x : E) (rhs : U32) (hrhs : rhs.val<2147483647) :
    ∃ z, field.wide_exact.WideExact.mul_m31 x rhs=.ok z ∧ CanonicalE z ∧
      decodeE z=decodeE x*embedding (scalarK rhs) := by
  obtain ⟨a,ha,hac,hav⟩ := k_mul_m31 x.c0 rhs
  obtain ⟨b,hb,hbc,hbv⟩ := k_mul_m31 x.c1 rhs
  refine ⟨⟨a,b⟩,?_,⟨hac,hbc⟩,?_⟩
  · simp only [field.wide_exact.WideExact.mul_m31,rem_identity rhs hrhs,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · simpa [decodeE,embedding] using hav
    · simpa [decodeE,embedding] using hbv

#print axioms scalar
end AspisR1.CuSavingsWideArithmetic
