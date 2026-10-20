import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Raw.Proofs
import Lean.Elab.Tactic.Omega

namespace CompPolyModularRemainderDegree
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem raw_modByMonic_size_le
    (p q : CPolynomial.Raw F) (hp : p.trim = p) (hq : q.trim = q)
    (hq0 : q ≠ (0 : CPolynomial.Raw F))
    (hqmonic : (CPolynomial.ofArray q).monic = true) :
    (CPolynomial.Raw.modByMonic p q).size ≤ q.size := by
  let r := CPolynomial.Raw.modByMonic p q
  have hrtrim : r.trim = r := CPolynomial.Raw.modByMonic_canonical hp q
  have hrem : CPolynomial.ofArray r =
      (CPolynomial.ofArray p).modByMonic (CPolynomial.ofArray q) := by
    apply CPolynomial.ext
    change r.trim = CPolynomial.Raw.modByMonic (p.trim) (q.trim)
    rw [hrtrim, hp, hq]
  have hpoly : (CPolynomial.ofArray r).toPoly =
      (CPolynomial.ofArray p).toPoly %ₘ (CPolynomial.ofArray q).toPoly := by
    rw [hrem]
    exact CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hqmonic
  have hnat : (CPolynomial.ofArray r).natDegree ≤
      (CPolynomial.ofArray q).natDegree := by
    rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, hpoly]
    exact Polynomial.natDegree_modByMonic_le _
      ((CPolynomial.monic_toPoly_iff (CPolynomial.ofArray q)).mp hqmonic)
  have size_eq_natDegree_of_trim (x : CPolynomial.Raw F)
      (hx : x.trim = x) (hx0 : x ≠ (0 : CPolynomial.Raw F)) :
      x.size = (CPolynomial.ofArray x).natDegree + 1 := by
    cases hs : x.size with
    | zero =>
        have : x = (0 : CPolynomial.Raw F) := Array.eq_empty_of_size_eq_zero hs
        exact False.elim (hx0 this)
    | succ n =>
        simp [CPolynomial.ofArray, CPolynomial.natDegree, hx, hs]
  by_cases hr0 : r = (0 : CPolynomial.Raw F)
  · simp [r, hr0]
  · have hrsize := size_eq_natDegree_of_trim r hrtrim hr0
    have hqsize := size_eq_natDegree_of_trim q hq hq0
    rw [hrsize, hqsize]
    exact Nat.add_le_add_right hnat 1

end CompPolyModularRemainderDegree
