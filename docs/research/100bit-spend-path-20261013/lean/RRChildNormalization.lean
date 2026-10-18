import RRRootDescent
import Mathlib.Algebra.Polynomial.Eval.Coeff

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]

/-- Proof-level specification of dropping `v` inner coefficients.
The executable coefficient-vector program refines this polynomial model. -/
def stripInnerPower (Q : (K[X])[X]) (v : Nat) : (K[X])[X] :=
  Q.sum fun j c => C (c /ₘ (X : K[X]) ^ v) * X ^ j

theorem stripInnerPower_coeff (Q : (K[X])[X]) (v j : Nat) :
    (stripInnerPower Q v).coeff j = Q.coeff j /ₘ (X : K[X]) ^ v := by
  classical
  unfold stripInnerPower
  rw [Polynomial.sum_def, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp only [coeff_C_mul_X_pow, ite_true]
  · intro b hb hbj
    have hjb : j ≠ b := fun h => hbj h.symm
    simp only [coeff_C_mul_X_pow, if_neg hjb]
  · intro hj
    have hz : Q.coeff j = 0 := Polynomial.notMem_support_iff.mp hj
    simp [hz]

/-- Vanishing lower inner slices justify the exact normalization factor. -/
theorem stripInnerPower_factor (Q : (K[X])[X]) (v : Nat)
    (hlower : ∀ j k, k < v → (Q.coeff j).coeff k = 0) :
    Q = C ((X : K[X]) ^ v) * stripInnerPower Q v := by
  ext j
  rw [coeff_C_mul, stripInnerPower_coeff]
  have hd : (X : K[X]) ^ v ∣ Q.coeff j :=
    Polynomial.X_pow_dvd_iff.mpr (fun k hk => hlower j k hk)
  obtain ⟨r, hr⟩ := hd
  rw [hr, Polynomial.mul_divByMonic_cancel_left r (monic_X.pow v)]

/-- Readback of coefficientwise division is exactly dropping the first `v`
inner coefficients; this is the refinement equation for a list.drop backend. -/
theorem stripInnerPower_coeff_readback (Q : (K[X])[X]) (v j k : Nat)
    (hlower : ∀ j k, k < v → (Q.coeff j).coeff k = 0) :
    ((stripInnerPower Q v).coeff j).coeff k = (Q.coeff j).coeff (v + k) := by
  have hfactor := stripInnerPower_factor Q v hlower
  have hcoeff := congrArg (fun p : (K[X])[X] => p.coeff j) hfactor
  rw [coeff_C_mul] at hcoeff
  rw [hcoeff, Nat.add_comm v k, Polynomial.coeff_X_pow_mul]

/-- The concrete coefficientwise normalization, with no factorization premise. -/
theorem stripInnerPower_preserves_roots
    (Q : (K[X])[X]) (a : K) (v : Nat) (g : K[X])
    (hlower : ∀ j k, k < v → ((Q.comp (affine a)).coeff j).coeff k = 0) :
    (stripInnerPower (Q.comp (affine a)) v).eval g = 0 ↔
      Q.eval (C a + X * g) = 0 := by
  exact normalized_child_root_iff Q _ a v g
    (stripInnerPower_factor (Q.comp (affine a)) v hlower)

#print axioms stripInnerPower_coeff
#print axioms stripInnerPower_coeff_readback
#print axioms stripInnerPower_factor
#print axioms stripInnerPower_preserves_roots
end RRRootDescent
