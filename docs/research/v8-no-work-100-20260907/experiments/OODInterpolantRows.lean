import OODInterpolantCore

/-! Actual x/y selection, gamma batches, chord signs, sparse interpolant and
ordinary affine correction. The source field inverse must supply Checked;
the two OOD answers themselves need not be correct or nonzero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 8000
namespace AspisV8.OODInterpolant
noncomputable section
open Polynomial AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriRelationCandidateBridge AspisV8.ChordPolynomialImage
open AspisV8.ShiftedRowPrefix AspisV8.InterleavedChordRows
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

structure Data where
  x0 : K
  y0 : K
  x1 : K
  y1 : K
  gamma : K
  answers : Fin 2 → Fin 29 → K
  inverse : K

def Data.useX (d : Data (K := K)) : Bool := decide (d.x0 ≠ d.x1)
def Data.h0 (d : Data (K := K)) : K := selected d.useX d.x0 d.y0
def Data.h1 (d : Data (K := K)) : K := selected d.useX d.x1 d.y1
def Data.batch (d : Data (K := K)) (r : Fin 2) : K :=
  ∑ lane, d.gamma^lane.val*d.answers r lane
def Data.Checked (d : Data (K := K)) : Prop := (d.h0-d.h1)*d.inverse=1
def Data.slope (d : Data (K := K)) : K :=
  OODInterpolant.slope d.h0 d.h1 (d.batch 0) (d.batch 1) d.inverse
def Data.intercept (d : Data (K := K)) : K :=
  OODInterpolant.intercept d.h0 d.h1 (d.batch 0) (d.batch 1) d.inverse
def Data.interpolant (d : Data (K := K)) : Fin 1024 → K :=
  vector d.useX d.intercept d.slope
def Data.a (d : Data (K := K)) : K := d.x0*d.y1-d.y0*d.x1
def Data.b (d : Data (K := K)) : K := d.y0-d.y1
def Data.c (d : Data (K := K)) : K := d.x1-d.x0

/-- A successful inverse boundary has no remaining prover/caller choice:
the inverse is uniquely determined by the already fixed point coordinates. -/
theorem Data.checked_inverse_eq (d : Data (K := K)) (checked : d.Checked) :
    d.inverse=(d.h0-d.h1)⁻¹ := by
  have hn := checked_nonzero (d.h0-d.h1) d.inverse checked
  have h := congrArg (fun z : K => (d.h0-d.h1)⁻¹*z) checked
  simpa only [inv_mul_cancel_left₀ hn,mul_one] using h

theorem Data.chord_at_points (d : Data (K := K)) :
    d.a+d.b*d.x0+d.c*d.y0=0 ∧ d.a+d.b*d.x1+d.c*d.y1=0 := by
  unfold Data.a Data.b Data.c
  constructor <;> ring

theorem Data.chord_nondegenerate (d : Data (K := K)) (checked : d.Checked) :
    d.b ≠ 0 ∨ d.c ≠ 0 := by
  have hn := checked_nonzero (d.h0-d.h1) d.inverse checked
  by_cases hx : d.x0 ≠ d.x1
  · exact Or.inr (sub_ne_zero.mpr (Ne.symm hx))
  · exact Or.inl (by simpa only [Data.h0,Data.h1,Data.b,selected,Data.useX,
      decide_eq_false hx, Bool.false_eq_true,if_false] using hn)

theorem Data.eval_at_points (d : Data (K := K)) (checked : d.Checked) :
    circleEval (initialP0 d.interpolant) (initialP1 d.interpolant) d.x0 d.y0=d.batch 0 ∧
    circleEval (initialP0 d.interpolant) (initialP1 d.interpolant) d.x1 d.y1=d.batch 1 := by
  unfold Data.interpolant
  rw [vector_eval,vector_eval]
  exact interpolation d.h0 d.h1 (d.batch 0) (d.batch 1) d.inverse checked

def ordinaryWeight {n : Nat} (w : Fin 4 → Fin n → K) (kappa : K) : Fin n → K :=
  fun i => w 0 i+kappa*w 1 i+kappa^2*w 2 i+kappa^3*w 3 i

theorem covector_apply {n : Nat} (w v : Fin n → K) :
    covector w v=candidateClaim w v := rfl

theorem ordinary_dot {n : Nat} (w : Fin 4 → Fin n → K) (kappa : K) (v : Fin n → K) :
    ClaimTransport.ordinary (covector (w 0)) (fun j : Fin 3 => covector (w j.succ)) kappa v=
      candidateClaim (ordinaryWeight w kappa) v := by
  simp only [ClaimTransport.ordinary,LinearMap.add_apply,LinearMap.smul_apply,covector_apply,
    candidateClaim,ordinaryWeight,smul_eq_mul,Finset.mul_sum,
    mul_add,Finset.sum_add_distrib,mul_left_comm]
  rfl

/-- Literal query-fibre order, not sorted coordinates or a renamed V7 word. -/
theorem vector_fibre (useX : Bool) (u v x y : K) :
    PostQueryFunctional.circleFibre (vector useX u v) x y=
      if useX then ![u+v*x,u+v*x,u-v*x,u-v*x]
      else ![u+v*y,u-v*y,u-v*y,u+v*y] := by
  have h (x y : K) : PostQueryFunctional.circleValue (vector useX u v) x y=
      u+v*selected useX x y := vector_eval useX u v x y
  unfold PostQueryFunctional.circleFibre
  simp_rw [h]
  cases useX <;> simp [selected,mul_neg,sub_eq_add_neg]

def Data.rows (d : Data (K := K)) (quarter : K) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 4 → K) (q : Fin 1024 → K) : Rows (K := K) :=
  InterleavedChordRows.rows d.a d.b d.c quarter w claimed q d.interpolant

/-- The two multiplications/subtractions actually performed by prepare(). -/
def Data.sourceClaim (d : Data (K := K)) (w : Fin 4 → Fin 1024 → K)
    (claimed : Fin 4 → K) (kappa : K) : K :=
  claimed 0+kappa*claimed 1+kappa^2*claimed 2+kappa^3*claimed 3
    -d.intercept*ordinaryWeight w kappa 0-d.slope*ordinaryWeight w kappa (slot d.useX)

theorem ordinary_interpolant (r : Rows (K := K)) (useX : Bool) (u v kappa : K) :
    r.ordinaryFunctional kappa (vector useX u v)=
      u*ordinaryWeight r.original kappa 0+v*ordinaryWeight r.original kappa (slot useX) := by
  unfold Rows.ordinaryFunctional Rows.functional
  rw [ordinary_dot,dot_vector]

/-- No functional/interpolant agreement is a premise: both sides use the
constructed sparse vector and the same four original covectors. -/
theorem Data.corrected_claim (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 4 → K) (q : Fin 1024 → K) (kappa : K) :
    (d.rows quarter w claimed q).correctedClaim kappa=d.sourceClaim w claimed kappa := by
  unfold Rows.correctedClaim Data.sourceClaim
  have hi : (d.rows quarter w claimed q).interpolant=vector d.useX d.intercept d.slope := rfl
  rw [hi,ordinary_interpolant]
  simp only [Data.rows,InterleavedChordRows.rows]
  ring

/-- The actual scalar subtraction and concrete chord transpose preserve the
existing four shifted-row discrepancy. Image constraints are not a premise. -/
theorem Data.source_prior (d : Data (K := K)) (quarter : K)
    (w : Fin 4 → Fin 1024 → K) (claimed : Fin 4 → K) (q : Fin 1024 → K) (kappa : K) :
    d.sourceClaim w claimed kappa-
      candidateClaim ((d.rows quarter w claimed q).transportedWeight kappa) q=
      ((d.rows quarter w claimed q).errorPolynomial).eval kappa := by
  rw [← d.corrected_claim quarter w claimed q kappa]
  exact before_prior (d.rows quarter w claimed q) kappa

#print axioms Data.chord_at_points
#print axioms Data.checked_inverse_eq
#print axioms Data.chord_nondegenerate
#print axioms Data.eval_at_points
#print axioms ordinary_dot
#print axioms vector_fibre
#print axioms Data.corrected_claim
#print axioms Data.source_prior
end
end AspisV8.OODInterpolant
