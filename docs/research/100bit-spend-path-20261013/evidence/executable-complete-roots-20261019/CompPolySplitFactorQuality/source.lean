import CompPolySplitRetries

noncomputable section
namespace AspisR1.CompPolySplitFactorQuality
open CompPoly Polynomial AspisR1.CompPolyPolynomialBackendBridge
open AspisR1.CompPolySplitTrial AspisR1.CompPolySplitRetries
open AspisR1.CantorZassenhausSplit
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

/-- Every accepted executable gcd is a monic proper divisor. -/
theorem gcd_quality (f h : CPolynomial K) (hf : f.toPoly.Monic)
    (hp : proper (CPolynomial.gcdMonic f h) f = true) :
    (CPolynomial.gcdMonic f h).toPoly.Monic ∧
      ProperFactor (CPolynomial.gcdMonic f h).toPoly f.toPoly := by
  refine ⟨?_, ?_, (proper_iff _ _).mp hp⟩
  · rw [gcd_backend_correct]
    exact monicGCD_monic _ _ hf.ne_zero
  · rw [gcd_backend_correct]
    exact monicGCD_dvd_left _ _

theorem trySplit_quality (f h d : CPolynomial K) (q : Nat)
    (hf : f.toPoly.Monic) (hs : trySplit f h q = some d) :
    d.toPoly.Monic ∧ ProperFactor d.toPoly f.toPoly := by
  unfold trySplit at hs
  dsimp only at hs
  split at hs
  · rename_i hp
    cases hs
    exact gcd_quality f h hf hp
  · split at hs
    · rename_i hp
      cases hs
      exact gcd_quality f _ hf hp
    · contradiction

theorem retry_quality (f d : CPolynomial K) (q t : Nat) (tape : Fin t → K × K)
    (hf : f.toPoly.Monic) (hs : retry f q t tape = some d) :
    d.toPoly.Monic ∧ ProperFactor d.toPoly f.toPoly := by
  induction t with
  | zero => simp [retry] at hs
  | succ t ih =>
    cases ht : trySplit f (linear (tape 0)) q with
    | none =>
      rw [retry, ht] at hs
      exact ih (fun i => tape i.succ) hs
    | some e =>
      rw [retry, ht] at hs
      cases hs
      exact trySplit_quality f _ d q hf ht

/-- Executable monic division gives two strictly smaller, positive-degree
monic children whose product is exactly the parent. -/
theorem complement_quality (f d : CPolynomial K) (hf : f.toPoly.Monic)
    (hd : d.toPoly.Monic) (hp : ProperFactor d.toPoly f.toPoly) :
    let e := f.divByMonic d
    d.toPoly * e.toPoly = f.toPoly ∧ e.toPoly.Monic ∧
      0 < d.toPoly.natDegree ∧ d.toPoly.natDegree < f.toPoly.natDegree ∧
      0 < e.toPoly.natDegree ∧ e.toPoly.natDegree < f.toPoly.natDegree := by
  dsimp only
  have hdc : d.monic := (CPolynomial.monic_toPoly_iff d).mpr hd
  rw [CPolynomial.divByMonic_toPoly_eq_divByMonic f d hdc]
  have hprod : d.toPoly * (f.toPoly /ₘ d.toPoly) = f.toPoly := by
    obtain ⟨e, he⟩ := hp.1
    rw [he, mul_divByMonic_cancel_left e hd]
  have hemonic := hd.of_mul_monic_left (hprod.symm ▸ hf)
  have hdeg := proper_monic_factor_degrees d.toPoly f.toPoly hd hf hp
  have hedeg : (f.toPoly /ₘ d.toPoly).natDegree =
      f.toPoly.natDegree - d.toPoly.natDegree := natDegree_divByMonic _ hd
  refine ⟨hprod, hemonic, hdeg.1, hdeg.2, ?_, ?_⟩ <;> omega

#print axioms gcd_quality
#print axioms trySplit_quality
#print axioms retry_quality
#print axioms complement_quality
end AspisR1.CompPolySplitFactorQuality
