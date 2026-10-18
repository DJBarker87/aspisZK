import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]

/-- Substitute the next coefficient `a`, retaining the formal tail variable. -/
def affine (a : K) : (K[X])[X] :=
  C (C a) + X * C (X : K[X])

theorem eval_affine (a : K) (g : K[X]) :
    (affine a).eval g = C a + X * g := by
  simp only [affine, eval_add, eval_C, eval_mul, eval_X]
  rw [mul_comm g X]

/-- Exact division by an inner-X power preserves every polynomial root
after the Roth--Ruckenstein affine substitution. No root is guessed here. -/
theorem normalized_child_root_iff
    (Q child : (K[X])[X]) (a : K) (v : Nat) (g : K[X])
    (hfactor : Q.comp (affine a) = C ((X : K[X]) ^ v) * child) :
    child.eval g = 0 ↔ Q.eval (C a + X * g) = 0 := by
  have heval := congrArg (fun p : (K[X])[X] => p.eval g) hfactor
  rw [eval_comp, eval_affine, eval_mul, eval_C] at heval
  constructor
  · intro h
    rw [heval, h, mul_zero]
  · intro h
    have hz : (X : K[X]) ^ v * child.eval g = 0 := heval.symm.trans h
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero v X_ne_zero)

/-- A root's constant coefficient must be one of the roots of the
coefficientwise inner-X=0 specialization. -/
theorem constant_coefficient_is_root (Q : (K[X])[X]) (f : K[X])
    (hroot : Q.eval f = 0) :
    (Q.map (Polynomial.evalRingHom (0 : K))).eval (f.eval 0) = 0 := by
  have h := congrArg (Polynomial.evalRingHom (0 : K)) hroot
  rw [Polynomial.eval_map]
  change Q.eval₂ (Polynomial.evalRingHom (0 : K)) ((Polynomial.evalRingHom (0 : K)) f) = 0
  rw [Polynomial.eval₂_hom]
  simpa only [map_zero] using h

/-- Every polynomial has the affine head/tail shape used by descent. -/
theorem head_tail (f : K[X]) : C (f.coeff 0) + X * f.divX = f := by
  simpa [add_comm] using Polynomial.X_mul_divX_add f

theorem descend_actual_root
    (Q child : (K[X])[X]) (v : Nat) (f : K[X])
    (hfactor : Q.comp (affine (f.coeff 0)) = C ((X : K[X]) ^ v) * child)
    (hroot : Q.eval f = 0) : child.eval f.divX = 0 := by
  apply (normalized_child_root_iff Q child (f.coeff 0) v f.divX hfactor).mpr
  simpa only [head_tail] using hroot

#print axioms normalized_child_root_iff
#print axioms constant_coefficient_is_root
#print axioms head_tail
#print axioms descend_actual_root
end RRRootDescent
