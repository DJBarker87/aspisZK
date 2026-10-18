import CompPolyFactorCertificate
import FiniteFieldNormalizedRootFactor

namespace AspisR1.CompPolyCompleteRoots
open CompPoly AspisR1.CompPolyPolynomialBackendBridge AspisR1.CompPolyFactorRecursion

def rootFactor {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q : Nat) : CPolynomial K :=
  CPolynomial.gcdMonic p (modPower CPolynomial.X p q - CPolynomial.X)

/-- Complete root finding by bounded randomized factorization of the
squarefree, split root factor. Failure is explicit, never enumeration. -/
def findRoots {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q t : Nat) (coins : Nat → Fin t → K × K) : Option (List K) :=
  factor q t coins (p.natDegree+1) 0 (rootFactor p q)

noncomputable section
open Polynomial AspisR1.CompPolyFactorCertificate
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem rootFactor_backend_correct (p : CPolynomial K) (q : Nat) (hp : p.toPoly.Monic) :
    (rootFactor p q).toPoly = FiniteFieldNormalizedRootFactor.rootFactor p.toPoly q := by
  rw [rootFactor, gcd_backend_correct, CPolynomial.toPoly_sub,
    modPower_backend_correct _ p hp, CPolynomial.X_toPoly]
  rfl

theorem findRoots_complete (p : CPolynomial K) (q t : Nat)
    (coins : Nat → Fin t → K × K) (roots : List K)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree)
    (hs : findRoots p q t coins = some roots) :
    (∀ x, IsRoot p.toPoly x ↔ x ∈ roots) ∧
      roots.Nodup ∧ roots.length ≤ p.toPoly.natDegree := by
  have hb := rootFactor_backend_correct p q hp
  have hm : (rootFactor p q).toPoly.Monic := by
    rw [hb]
    exact FiniteFieldNormalizedRootFactor.rootFactor_monic _ _ hp.ne_zero
  have hc := factor_complete q t coins (p.natDegree+1) 0 (rootFactor p q) roots hm hs
  have hprod : linearProduct roots = (rootFactor p q).toPoly :=
    factor_product q t coins (p.natDegree+1) 0 (rootFactor p q) roots hm hs
  have hsep : (linearProduct roots).Separable := by
    rw [hprod, hb]
    exact FiniteFieldNormalizedRootFactor.rootFactor_separable _ _ hq hp hdeg
  have hn : (roots : Multiset K).Nodup :=
    Polynomial.nodup_of_separable_prod (by simpa [linearProduct] using hsep)
  refine ⟨?_, hn, ?_⟩
  · intro x
    rw [← hc.1 x, hb]
    exact (FiniteFieldNormalizedRootFactor.rootFactor_roots_iff _ _ hq hp hdeg x).symm
  · rw [hc.2, hb]
    exact Polynomial.natDegree_le_of_dvd
      (FiniteFieldNormalizedRootFactor.rootFactor_dvd _ _) hp.ne_zero

#print axioms rootFactor_backend_correct
#print axioms findRoots_complete
end
end AspisR1.CompPolyCompleteRoots
