import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.FinCases
import AspisV8R19.R744JointEntryHom

/-! A symbolic polynomial presentation of the R743 ordinary joint rows. -/
set_option autoImplicit false
namespace AspisV8R19.R745JointObservationPolynomial
open MvPolynomial
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R744JointEntryHom
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F] [Nontrivial F]

abbrev JointPoly (F : Type*) [CommRing F] := MvPolynomial (Fin 15) F
abbrev ObservationRow := R738JointObservationModel.ObservationRow

def assignment (alpha u v kappa tau : F) (z : Fin 10 → F) : Fin 15 → F :=
  Fin.cases alpha (Fin.cases u (Fin.cases v (Fin.cases kappa (Fin.cases tau z))))

def pAlpha : JointPoly F := X 0
def pU : JointPoly F := X 1
def pV : JointPoly F := X 2
def pKappa : JointPoly F := X 3
def pTau : JointPoly F := X 4
def pZ (j : Fin 10) : JointPoly F := X (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ j)))))

def polynomialABC : Fin 3 → JointPoly F
  | ⟨0, _⟩ => 1 + pU * pV
  | ⟨1, _⟩ => pU * pV - 1
  | ⟨2, _⟩ => -(pU + pV)

def qdiff (d : Fin 255) (s : Fin 3) : Nat → F :=
  fun r => unitVector (4*d.val+s.val+1) r - unitVector (s.val+1) r

def sdiff (d : Fin 255) : Nat → F :=
  fun r => unitVector (4*d.val) r - unitVector 0 r

def polynomialEntry (half quarter : F) (d : Fin 255) (s : Fin 3) :
    ObservationRow → JointPoly F
  | .inl j =>
      ∑ l : Fin 3, polynomialABC l *
        (C (sourceBasisConstants half (qdiff d s) (R707FullActiveDeterminant.rowCode j) l) -
          pAlpha^(s.val+1) * C (sourceBasisConstants half (sdiff d) (R707FullActiveDeterminant.rowCode j) l))
  | .inr row =>
      sparseObservation (C half) (C quarter) (1+pU*pV) (pU*pV-1) (-(pU+pV))
        pKappa pTau pAlpha pZ d s (.inr row)

theorem eval_polynomialEntry (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3) (row : ObservationRow) :
    eval (assignment alpha u v kappa tau z) (polynomialEntry half quarter d s row) =
      rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (indexedDirection alpha d s) row := by
  rcases row with j | ⟨p | k⟩
  · simp only [polynomialEntry, rawObservation]
    have hα : assignment alpha u v kappa tau z 0 = alpha := rfl
    have hu : assignment alpha u v kappa tau z 1 = u := rfl
    have hv : assignment alpha u v kappa tau z 2 = v := rfl
    rw [Fin.sum_univ_succ]
    simp [polynomialABC, pAlpha, pU, pV, hα, hu, hv]
    have hq : (fun i => qdiff d s i-alpha^(s.val+1)*sdiff d i) = direction alpha d s := by
      funext i
      unfold qdiff sdiff direction qPair
      simp only [Fin.val_zero, Nat.mul_zero, zero_add]
      ring
    rw [← rawFlatten_indexedDirection, hq]
    exact (sourceChord_six_constants half (qdiff d s) (sdiff d)
      (1+u*v) (u*v-1) (-(u+v)) (alpha^(s.val+1))
      (R707FullActiveDeterminant.rowCode j)).symm
  · change eval (assignment alpha u v kappa tau z)
      (sparseObservation (C half) (C quarter) (1+pU*pV) (pU*pV-1) (-(pU+pV))
        pKappa pTau pAlpha pZ d s (.inr (.inl p))) = _
    have h := map_sparse_point_row (eval (assignment alpha u v kappa tau z))
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau alpha z d s p
    simpa [assignment,pAlpha,pU,pV,pKappa,pTau,pZ] using h
  · change eval (assignment alpha u v kappa tau z)
      (sparseObservation (C half) (C quarter) (1+pU*pV) (pU*pV-1) (-(pU+pV))
        pKappa pTau pAlpha pZ d s (.inr (.inr k))) = _
    have h := map_sparse_coefficient_row (eval (assignment alpha u v kappa tau z))
      half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau alpha z d s k
    simpa [assignment,pAlpha,pU,pV,pKappa,pTau,pZ] using h

def polynomialMatrix (half quarter : F) (cols : ObservationRow → Fin 255 × Fin 3) :
    Matrix ObservationRow ObservationRow (JointPoly F) :=
  fun row col => polynomialEntry half quarter col.1 col.2 row

theorem eval_polynomialMatrix (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (cols : ObservationRow → Fin 255 × Fin 3) :
    (eval (assignment alpha u v kappa tau z)).mapMatrix (polynomialMatrix half quarter cols) =
      fun row col => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (indexedDirection alpha col.1 col.2) row := by
  ext row col
  exact eval_polynomialEntry half quarter alpha u v kappa tau z col.1 col.2 row

theorem eval_polynomialMatrix_det [Fintype ObservationRow] [DecidableEq ObservationRow]
    (half quarter alpha u v kappa tau : F)
    (z : Fin 10 → F) (cols : ObservationRow → Fin 255 × Fin 3) :
    eval (assignment alpha u v kappa tau z) (polynomialMatrix half quarter cols).det =
      Matrix.det (fun row col => rawObservation half quarter (1+u*v) (u*v-1) (-(u+v)) kappa tau z
        (indexedDirection alpha (cols col).1 (cols col).2) row) := by
  rw [(eval (assignment alpha u v kappa tau z)).map_det, eval_polynomialMatrix]

#print axioms eval_polynomialEntry
#print axioms eval_polynomialMatrix
#print axioms eval_polynomialMatrix_det
end
end AspisV8R19.R745JointObservationPolynomial
