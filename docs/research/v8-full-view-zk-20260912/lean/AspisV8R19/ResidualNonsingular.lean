/- A checked right inverse suffices; no trusted determinant evaluator. -/
import AspisV8R19.ResidualEntryCertificate

namespace AspisR19.ResidualNonsingular
variable {F : Type*} [CommRing F]

theorem right_inverse_det_ne_zero [Nontrivial F] (a b : Matrix (Fin 13) (Fin 13) F)
    (h : a*b=1) : a.det ≠ 0 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  intro hz
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

theorem polynomial_nonzero (half quarter : F) (s : Fin 36 → F)
    (h : (SourceResidualPolynomial.assignedMinor half quarter s).det ≠ 0) :
    (SourceResidualPolynomial.polyMinor half quarter).det ≠ 0 := by
  intro hz
  have he := SourceResidualPolynomial.determinant_evaluation half quarter s
  rw [hz, map_zero] at he
  exact h he.symm

#print axioms right_inverse_det_ne_zero
#print axioms polynomial_nonzero
end AspisR19.ResidualNonsingular
