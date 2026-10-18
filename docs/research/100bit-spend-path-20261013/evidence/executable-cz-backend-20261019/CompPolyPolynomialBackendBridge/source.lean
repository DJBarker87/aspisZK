import CompPoly.Univariate.EuclideanAlgorithm
import CantorZassenhausFastTrial
import Mathlib.Data.ZMod.Basic

namespace AspisR1.CompPolyPolynomialBackendBridge
open CompPoly

/-- Same binary recursion as the existing proved specification, with
computable polynomial arithmetic supplied by the pinned CompPoly backend. -/
def modPower {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (a m : CPolynomial K) : Nat → CPolynomial K :=
  Nat.binaryRec 1 (fun b _ z => (z * z * (if b then a else 1)).modByMonic m)

noncomputable section
open Polynomial AspisR1.CantorZassenhausSplit
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

omit [Fintype K] in
theorem gcd_backend_correct (p q : CPolynomial K) :
    (CPolynomial.gcdMonic p q).toPoly = monicGCD p.toPoly q.toPoly := by
  exact CPolynomial.gcdMonic_toPoly_eq_normalize_gcd p q

theorem modPower_backend_correct (a m : CPolynomial K)
    (hm : m.toPoly.Monic) (e : Nat) :
    (modPower a m e).toPoly = polynomialModPower a.toPoly m.toPoly e := by
  have hm' : m.monic := (CPolynomial.monic_toPoly_iff m).mpr hm
  refine Nat.binaryRec (motive := fun n =>
    (modPower a m n).toPoly = polynomialModPower a.toPoly m.toPoly n) ?_ ?_ e
  · simp [modPower, polynomialModPower, CPolynomial.toPoly_one]
  · intro b n ih
    by_cases hz : Nat.bit b n = 0
    · rw [hz]
      simp [modPower, polynomialModPower, CPolynomial.toPoly_one]
    · have hcond : n = 0 → b = true := by
        intro hn
        subst n
        cases b with
        | false => exact False.elim (hz rfl)
        | true => rfl
      unfold modPower polynomialModPower
      rw [Nat.binaryRec_eq b n (Or.inr hcond), Nat.binaryRec_eq b n (Or.inr hcond)]
      rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hm']
      simp only [CPolynomial.toPoly_mul]
      change (modPower a m n).toPoly * (modPower a m n).toPoly *
        (if b then a else 1).toPoly %ₘ m.toPoly = _
      rw [ih]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
        CPolynomial.toPoly_one] <;> rfl

#print axioms gcd_backend_correct
#print axioms modPower_backend_correct
end

section
local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
private def x7 : CPolynomial (ZMod 7) := CPolynomial.X
private def f7 : CPolynomial (ZMod 7) := (x7 - 1) * (x7 - CPolynomial.C 2)
#eval let g := CPolynomial.gcdMonic f7 (x7 - 1); (g.coeff 0, g.coeff 1)
#eval let p := modPower x7 f7 3; (p.coeff 0, p.coeff 1)
end

#print axioms modPower
end AspisR1.CompPolyPolynomialBackendBridge
