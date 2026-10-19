import WideExactInitialInverseComputableV2
import CompPoly.Univariate.ToPoly.Impl

set_option autoImplicit false
namespace AspisWide.InitialParityCBridgeV9
open CompPoly
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [NeZero (2 : K)]

def evenC (q : CPolynomial K) : CPolynomial K :=
  CPolynomial.ofArray (Array.ofFn fun i : Fin 513 => q.coeff (2 * i.val))
def oddC (q : CPolynomial K) : CPolynomial K :=
  CPolynomial.ofArray (Array.ofFn fun i : Fin 512 => (2 : K)⁻¹ * q.coeff (2 * i.val + 1))

theorem evenC_coeff (q : CPolynomial K) (n : Nat) :
    (evenC q).toPoly.coeff n = if n < 513 then q.toPoly.coeff (2 * n) else 0 := by
  rw [← CPolynomial.coeff_toPoly (evenC q) n]
  change (CPolynomial.ofArray (Array.ofFn fun i : Fin 513 => q.coeff (2 * i.val))).coeff n = _
  rw [CPolynomial.coeff_ofArray]
  by_cases hn : n < 513
  · simp [hn, Array.getD_eq_getD_getElem?]
    rw [← CPolynomial.coeff_toPoly q (2 * n)]
    simp [CPolynomial.coeff, CPolynomial.Raw.coeff]
  · simp [hn, Array.getD_eq_getD_getElem?]

theorem oddC_coeff (q : CPolynomial K) (n : Nat) :
    (oddC q).toPoly.coeff n = if n < 512 then (2 : K)⁻¹ * q.toPoly.coeff (2 * n + 1) else 0 := by
  rw [← CPolynomial.coeff_toPoly (oddC q) n]
  change (CPolynomial.ofArray (Array.ofFn fun i : Fin 512 => (2 : K)⁻¹ * q.coeff (2 * i.val + 1))).coeff n = _
  rw [CPolynomial.coeff_ofArray]
  by_cases hn : n < 512
  · simp [hn, Array.getD_eq_getD_getElem?, NeZero.ne (2 : K)]
    rw [← CPolynomial.coeff_toPoly q (2 * n + 1)]
    simp [CPolynomial.coeff, CPolynomial.Raw.coeff]
  · simp [hn, Array.getD_eq_getD_getElem?]

#print axioms evenC_coeff
#print axioms oddC_coeff
end AspisWide.InitialParityCBridgeV9
