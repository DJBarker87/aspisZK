/- A concrete polynomial matrix for the pinned low residual arithmetic.
   No determinant nonvanishing or challenge distribution is assumed/proved. -/
import AspisV8R19.ResidualPins

namespace AspisR19.ResidualPolynomial
open MvPolynomial ResidualModel ResidualPins
variable {F : Type*} [CommRing F]
noncomputable section

/- Variables 0..9=z, 10=kappa, 11=alpha, 12..14=actual chord a,b,c,
   15..37=the 23 natural coefficients of the query-root polynomial. -/
def polyMinor (half quarter : F) : Matrix (Fin 13) (Fin 13) (MvPolynomial (Fin 38) F) :=
  minor order inactive (C half) (C quarter) (X 12) (X 13) (X 14) (X 10) (X 11)
    (fun i => X ⟨i.val,by omega⟩) (fun i => X ⟨15+i.val,by omega⟩)

def assignedMinor (half quarter : F) (s : Fin 38 → F) : Matrix (Fin 13) (Fin 13) F :=
  minor order inactive half quarter (s 12) (s 13) (s 14) (s 10) (s 11)
    (fun i => s ⟨i.val,by omega⟩) (fun i => s ⟨15+i.val,by omega⟩)

theorem entry_evaluation (half quarter : F) (s : Fin 38 → F) (i j : Fin 13) :
    eval s (polyMinor half quarter i j)=assignedMinor half quarter s i j := by
  unfold polyMinor assignedMinor minor
  rw [map_observation]
  simp only [eval_C,eval_X]

theorem matrix_evaluation (half quarter : F) (s : Fin 38 → F) :
    (eval s).mapMatrix (polyMinor half quarter)=assignedMinor half quarter s := by
  ext i j
  exact entry_evaluation half quarter s i j

theorem determinant_evaluation (half quarter : F) (s : Fin 38 → F) :
    eval s (polyMinor half quarter).det=(assignedMinor half quarter s).det := by
  rw [(eval s).map_det,matrix_evaluation]

#print axioms entry_evaluation
#print axioms matrix_evaluation
#print axioms determinant_evaluation
end
end AspisR19.ResidualPolynomial
