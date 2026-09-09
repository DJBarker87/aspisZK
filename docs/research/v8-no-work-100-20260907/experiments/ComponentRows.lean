import OODInterpolantRows

/-! Actual gamma powers and the repaired ordinary row constructor. Component
claims and weights are fixed before gamma; the inactive claim may depend on
gamma but precedes kappa. Representation of the reconstructed original
message is a recovery premise here, to be supplied by the selected cover.
No decoder success or correctly claimed point value is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 200
namespace AspisV8.ComponentRows
open Polynomial
open AspisV8.OODInterpolant AspisV8.ShiftedRowPrefix
open AspisV8.ClaimTransport AspisV8.InterleavedChordRows
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]
noncomputable section

def claimedRows (gamma inactive : K) (claimed : Fin 3 → Fin 29 → K) : Fin 4 → K :=
  ![inactive, ∑ lane, gamma^lane.val*claimed 0 lane,
    ∑ lane, gamma^lane.val*claimed 1 lane, ∑ lane, gamma^lane.val*claimed 2 lane]

theorem claimedRows_inactive (gamma inactive : K) (claimed : Fin 3 → Fin 29 → K) :
    claimedRows gamma inactive claimed 0=inactive := rfl

theorem claimedRows_point (gamma inactive : K) (claimed : Fin 3 → Fin 29 → K)
    (j : Fin 3) :
    claimedRows gamma inactive claimed j.succ=∑ lane, gamma^lane.val*claimed j lane := by
  fin_cases j <;> rfl

def rows (d : Data (K := K)) (quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 3 → Fin 29 → K) (inactive : K) (Q : Fin 1024 → K) : Rows (K := K) :=
  d.rows quarter w (claimedRows d.gamma inactive claimed) Q

def original (d : Data (K := K)) (Q : Fin 1024 → K) : Fin 1024 → K :=
  reconstruction d.a d.b d.c Q+d.interpolant

/-- The scalar actually enters the existing affine corrected constructor,
not a separate game assembled from supplied component-error equalities. -/
theorem source_claim (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K)
    (inactive : K) (Q : Fin 1024 → K) (kappa : K) :
    (rows d quarter w claimed inactive Q).correctedClaim kappa=
      d.sourceClaim w (claimedRows d.gamma inactive claimed) kappa :=
  d.corrected_claim quarter w (claimedRows d.gamma inactive claimed) Q kappa

theorem point_error (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K)
    (inactive : K) (Q : Fin 1024 → K) (j : Fin 3) :
    (rows d quarter w claimed inactive Q).errors j.succ=
      (∑ lane, d.gamma^lane.val*claimed j lane)-covector (w j.succ) (original d Q) := by
  change claimedRows d.gamma inactive claimed j.succ-_= _
  rw [claimedRows_point]
  rfl

/-- Recovery supplies an equality of concrete original message coefficients.
The row discrepancy then follows from the real scalar-power construction. -/
theorem recovered_point_error (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K)
    (inactive : K) (Q : Fin 1024 → K) (p : Fin 29 → Fin 1024 → K)
    (recovered : original d Q=batch d.gamma p) (j : Fin 3) :
    (rows d quarter w claimed inactive Q).errors j.succ=
      (errorPolynomial (covector (w j.succ)) p (claimed j)).eval d.gamma := by
  rw [point_error,recovered]
  exact component_error_eval (covector (w j.succ)) p (claimed j) d.gamma

theorem nonzero_component_error_forces_wrong_rows (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 3 → Fin 29 → K)
    (inactive : K) (Q : Fin 1024 → K) (p : Fin 29 → Fin 1024 → K)
    (recovered : original d Q=batch d.gamma p) (j : Fin 3)
    (nonzero : (errorPolynomial (covector (w j.succ)) p (claimed j)).eval d.gamma≠0) :
    (rows d quarter w claimed inactive Q).errors≠0 := by
  intro zero
  apply nonzero
  rw [← recovered_point_error d quarter w claimed inactive Q p recovered j,zero]
  rfl

#print axioms claimedRows_point
#print axioms source_claim
#print axioms point_error
#print axioms recovered_point_error
#print axioms nonzero_component_error_forces_wrong_rows
end
end AspisV8.ComponentRows
