import InterleavedChordRows

/-! Sparse two-entry OOD interpolant. All identities are derived from the
literal scalar arithmetic and existing low-bit natural coefficient convention.
No codeword/response correctness is assumed for the two supplied values. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 8000
namespace AspisV8.OODInterpolant
noncomputable section
open Polynomial AspisCircleTensorBinding
open AspisV5FriInitialCircleEncoderIdentity AspisV5FriRelationCandidateBridge
open AspisV8.NaturalChordImage AspisV8.InterleavedChordLinear
open AspisV8.ChordPolynomialImage AspisV8.ShiftedRowPrefix
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

def selected (useX : Bool) (x y : K) : K := if useX then x else y
def slot (useX : Bool) : Fin 1024 := if useX then 2 else 1
def slope (h0 h1 y0 y1 inverse : K) : K := (y0-y1)*inverse
def intercept (h0 h1 y0 y1 inverse : K) : K :=
  y0-slope h0 h1 y0 y1 inverse*h0
def vector (useX : Bool) (u v : K) : Fin 1024 → K :=
  Pi.single 0 u+Pi.single (slot useX) v

theorem checked_nonzero (d inverse : K) (checked : d*inverse=1) : d ≠ 0 := by
  intro hz
  simp only [hz,zero_mul] at checked
  exact zero_ne_one checked

theorem interpolation (h0 h1 y0 y1 inverse : K)
    (checked : (h0-h1)*inverse=1) :
    intercept h0 h1 y0 y1 inverse+slope h0 h1 y0 y1 inverse*h0=y0 ∧
    intercept h0 h1 y0 y1 inverse+slope h0 h1 y0 y1 inverse*h1=y1 := by
  constructor
  · unfold intercept; ring
  · unfold intercept slope
    linear_combination -(y0-y1)*checked

theorem dot_vector (useX : Bool) (u v : K) (w : Fin 1024 → K) :
    candidateClaim w (vector useX u v)=u*w 0+v*w (slot useX) := by
  simp [candidateClaim,vector,Finset.sum_add_distrib,add_mul,Pi.single_apply]

theorem line_single {n : Nat} (j : Fin n) (a : K) :
    line (Pi.single j a)=C a*naturalLinePoly K j.val := by
  classical
  unfold line
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_apply,hij]
  · simp
theorem line_add {n : Nat} (u v : Fin n → K) : line (u+v)=line u+line v := by
  exact (lineLinear n).map_add u v
theorem line_zero {n : Nat} : line (0 : Fin n → K)=0 := by simp [line]
theorem basis_zero : naturalLinePoly K 0=1 := by simp [naturalLinePoly]
theorem basis_one : naturalLinePoly K 1=X := by
  have h := basis_low_bit (K := K) 0
  simpa only [Nat.mul_zero,Nat.zero_add,basis_zero,mul_one] using h

theorem even_vector_x (u v : K) :
    evenCoefficients (vector true u v)=
      (Pi.single 0 u : Fin 512 → K)+(Pi.single 1 v : Fin 512 → K) := by
  funext i
  simp only [evenCoefficients,vector,slot,ite_true,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  split_ifs <;> simp_all <;> omega
theorem odd_vector_x (u v : K) :
    oddCoefficients (vector true u v)=(0 : Fin 512 → K) := by
  funext i
  simp only [oddCoefficients,vector,slot,ite_true,Pi.add_apply,Pi.single_apply,Fin.ext_iff,
    Pi.zero_apply]
  split_ifs <;> simp_all <;> omega
theorem even_vector_y (u v : K) :
    evenCoefficients (vector false u v)=Pi.single (0:Fin 512) u := by
  funext i
  simp only [evenCoefficients,vector,slot,ite_false,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  split_ifs <;> simp_all <;> omega
theorem odd_vector_y (u v : K) :
    oddCoefficients (vector false u v)=Pi.single (0:Fin 512) v := by
  funext i
  simp only [oddCoefficients,vector,slot,ite_false,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem vector_eval (useX : Bool) (u v x y : K) :
    circleEval (initialP0 (vector useX u v)) (initialP1 (vector useX u v)) x y=
      u+v*selected useX x y := by
  have hp0 (q : Fin 1024 → K) : initialP0 q=line (evenCoefficients (n := 512) q) :=
    by
      unfold initialP0
      exact line_polynomial (K := K) (n := 512) (by decide) (evenCoefficients (n := 512) q)
  have hp1 (q : Fin 1024 → K) : initialP1 q=line (oddCoefficients (n := 512) q) :=
    by
      unfold initialP1
      exact line_polynomial (K := K) (n := 512) (by decide) (oddCoefficients (n := 512) q)
  rw [hp0,hp1]
  cases useX
  · rw [even_vector_y,odd_vector_y,line_single,line_single]
    simp only [Fin.val_zero,basis_zero,mul_one,circleEval,eval_C,selected,
      Bool.false_eq_true,ite_false]
    ring
  · rw [even_vector_x,odd_vector_x,line_add,line_single,line_single,line_zero]
    simp only [Fin.val_zero,Fin.val_one,basis_zero,basis_one,mul_one,circleEval,
      eval_add,eval_mul,eval_C,eval_X,eval_zero,mul_zero,add_zero,selected,ite_true]

#print axioms interpolation
#print axioms dot_vector
#print axioms vector_eval
end
end AspisV8.OODInterpolant
