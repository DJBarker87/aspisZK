import FJa_BoxedSelAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_LiteralNonvacuity
open FIv_NativeValue (K)
/-- Unconditional literal partition-of-unity witness for ANY point, using
the retained symbolic theorem, never enumerating1024 rows. -/
theorem mass (alpha : Fin 10 → K) :
    (∑ r : Fin 1024,R0P.SemSource.selAt alpha r)=1 := by
  simp_rw [R0P.SemDegree.selAt_eq_bitWeight]
  exact R0P.SemDegree.bitWeight_sum 10 alpha
/-- Literal selector meaning and mass1 cannot be satisfied only by zero
weights. This is local non-vacuity, not a complete accepted-run fixture. -/
theorem nonzero (alpha : Fin 10 → K) : ∃ r : Fin 1024,R0P.SemSource.selAt alpha r≠0 := by
  by_contra h
  have all : ∀ r : Fin 1024,R0P.SemSource.selAt alpha r=0 := by simpa using h
  have sum := mass alpha
  simp only [all,Finset.sum_const_zero] at sum
  exact zero_ne_one sum
#print axioms mass
#print axioms nonzero
end AspisR1.FJa_LiteralNonvacuity
end
