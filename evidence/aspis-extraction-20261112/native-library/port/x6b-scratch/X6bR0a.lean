import R0.Fold
import Wide.EncoderLinearity

/-! X6b scratch bisection of R0.PolynomialPair.truncate_eq (tool, nothing proved).
`sorry` appears only in this scratch file, never in the ported tree. -/
set_option autoImplicit false
namespace AspisR0.PolynomialPair
open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriConcreteEncoderApplicability AspisV5FriInitialCircleEncoderIdentity
open AspisWide.InitialEncoder AspisWide.FinalEncoder AspisWide.Agreement
open AspisV7ExactOneFoldDomains AspisCircleGroupOrder
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def truncate (p : K[X]) : K[X] := monomialPolynomial (fun i : Fin 512 => p.coeff i)

-- t1: carried first bullet alone (second bullet sorry)
theorem t1 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · exact monomialPolynomial_coeff _ ⟨n, hn⟩
  · sorry

-- t7: carried second bullet alone (first bullet sorry)
theorem t7 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · sorry
  · rw [truncate, monomialPolynomial_coeff_eq_zero_of_ge _ _ (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n)]

-- t2: coefficient function given explicitly
theorem t2 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · exact monomialPolynomial_coeff (fun i : Fin 512 => p.coeff i) ⟨n, hn⟩
  · sorry

-- t3: unfold truncate first, then the carried exact
theorem t3 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · unfold truncate
    exact monomialPolynomial_coeff _ ⟨n, hn⟩
  · sorry

-- t4: the dependency's own pattern (monomialPolynomial_complete): change, then exact
theorem t4 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · change (monomialPolynomial (fun i : Fin 512 => p.coeff i)).coeff (⟨n, hn⟩ : Fin 512) =
      p.coeff (⟨n, hn⟩ : Fin 512)
    exact monomialPolynomial_coeff _ _
  · sorry

-- t8: t1 under the isDefEq trace
set_option trace.Meta.isDefEq true in
theorem t8 (p : K[X]) (hp : p.natDegree ≤ 511) : truncate p = p := by
  ext n
  by_cases hn : n < 512
  · exact monomialPolynomial_coeff _ ⟨n, hn⟩
  · sorry

end
end AspisR0.PolynomialPair
