import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

open Polynomial
noncomputable section

namespace RRRootMultiplicityTaylor

variable {K : Type*} [Field K]

/-- Below the root multiplicity, every Taylor coefficient vanishes. This is
stated with Hasse/Taylor coefficients, so it does not divide by factorials and
is valid in every characteristic. -/
theorem taylor_coeff_eq_zero_below_rootMultiplicity
    (p : K[X]) (a : K) (hp : p ≠ 0) {j : Nat}
    (hj : j < p.rootMultiplicity a) :
    (Polynomial.taylor a p).coeff j = 0 := by
  obtain ⟨q, hfactor, hnotdvd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hlinear : Polynomial.taylor a (X - C a) = X := by
    simp [Polynomial.taylor_apply]
  have htaylor : Polynomial.taylor a p =
      X ^ p.rootMultiplicity a * Polynomial.taylor a q := by
    calc
      Polynomial.taylor a p =
          Polynomial.taylor a ((X - C a) ^ p.rootMultiplicity a * q) :=
            congrArg (Polynomial.taylor a) hfactor
      _ = X ^ p.rootMultiplicity a * Polynomial.taylor a q := by
            rw [Polynomial.taylor_mul, Polynomial.taylor_pow, hlinear]
  have hdiv : X ^ p.rootMultiplicity a ∣ Polynomial.taylor a p :=
    ⟨Polynomial.taylor a q, htaylor⟩
  exact (Polynomial.X_pow_dvd_iff.mp hdiv) j hj

/-- The coefficient at the root multiplicity is nonzero. Together with the
previous lemma, this identifies the exact first nonzero Hasse-Taylor order. -/
theorem taylor_coeff_ne_zero_at_rootMultiplicity
    (p : K[X]) (a : K) (hp : p ≠ 0) :
    (Polynomial.taylor a p).coeff (p.rootMultiplicity a) ≠ 0 := by
  obtain ⟨q, hfactor, hnotdvd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hlinear : Polynomial.taylor a (X - C a) = X := by
    simp [Polynomial.taylor_apply]
  have htaylor : Polynomial.taylor a p =
      X ^ p.rootMultiplicity a * Polynomial.taylor a q := by
    calc
      Polynomial.taylor a p =
          Polynomial.taylor a ((X - C a) ^ p.rootMultiplicity a * q) :=
            congrArg (Polynomial.taylor a) hfactor
      _ = X ^ p.rootMultiplicity a * Polynomial.taylor a q := by
            rw [Polynomial.taylor_mul, Polynomial.taylor_pow, hlinear]
  have hcoeff :
      (Polynomial.taylor a p).coeff (p.rootMultiplicity a) = q.eval a := by
    rw [htaylor, Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      Polynomial.taylor_coeff_zero]
  have hnotroot : ¬ q.IsRoot a := by
    intro hroot
    exact hnotdvd (Polynomial.dvd_iff_isRoot.mpr hroot)
  intro hzero
  apply hnotroot
  rw [Polynomial.IsRoot]
  rw [← hcoeff, hzero]

#print axioms taylor_coeff_eq_zero_below_rootMultiplicity
#print axioms taylor_coeff_ne_zero_at_rootMultiplicity

end RRRootMultiplicityTaylor
