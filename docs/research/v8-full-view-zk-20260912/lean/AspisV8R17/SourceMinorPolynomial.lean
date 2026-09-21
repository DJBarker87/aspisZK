import AspisV8R17.ActiveEntry
import AspisV8R17.MinorDegree
import AspisV8R17.SourceMinor

/-! Concrete polynomial minor on the frozen source indices. Evaluation and
degree are symbolic; no determinant or source scatter is expanded. -/
set_option autoImplicit false
namespace AspisV8R17.SourceMinor
noncomputable section
open MvPolynomial
variable {F : Type*} [CommRing F] [Nontrivial F]

def polynomialEntry (half : F) (r col : ℕ) : ActivePoly F :=
  let base := 4*(22+col/3)
  let channel := 1+col%3
  activeEntry (sourceBasisConstants half (unitVector (base+channel)) r)
    (sourceBasisConstants half (unitVector base) r) channel

def polynomialMinor (half : F) : Matrix (Fin 214) (Fin 214) (ActivePoly F) :=
  fun i j => polynomialEntry half (sourceRows.getD i.val 0) (selectedColumns.getD j.val 0)

theorem polynomialEntry_eval (half alpha u v : F) (r col : ℕ) :
    eval (activeAssignment alpha u v) (polynomialEntry half r col) =
      entry half alpha (1+u*v) (u*v-1) (-(u+v)) r col := by
  unfold polynomialEntry entry
  exact sourceEntry_eval _ _ _ _ _ _ _ _

theorem polynomialEntry_degree (half : F) (r col : ℕ) :
    (polynomialEntry half r col).totalDegree ≤ 5 := by
  unfold polynomialEntry
  apply sourceEntry_degree
  have hm := Nat.mod_lt col (by decide : 0<3)
  omega

theorem polynomialMinor_eval (half alpha u v : F) :
    (eval (activeAssignment alpha u v)).mapMatrix (polynomialMinor half) =
      minor half alpha (1+u*v) (u*v-1) (-(u+v)) := by
  ext i j
  exact polynomialEntry_eval _ _ _ _ _ _

theorem polynomialMinor_det_eval (half alpha u v : F) :
    eval (activeAssignment alpha u v) (polynomialMinor half).det =
      Matrix.det (minor half alpha (1+u*v) (u*v-1) (-(u+v))) := by
  rw [(eval (activeAssignment alpha u v)).map_det, polynomialMinor_eval]

theorem polynomialMinor_det_degree (half : F) :
    (polynomialMinor half).det.totalDegree ≤ 1070 := by
  have h := minor_totalDegree (polynomialMinor half) 5 (fun i j => polynomialEntry_degree half _ _)
  simpa using h

#print axioms polynomialEntry_eval
#print axioms polynomialEntry_degree
#print axioms polynomialMinor_eval
#print axioms polynomialMinor_det_eval
#print axioms polynomialMinor_det_degree
end
end AspisV8R17.SourceMinor
