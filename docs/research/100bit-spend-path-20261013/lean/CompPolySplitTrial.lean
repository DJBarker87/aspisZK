import CompPolyPolynomialBackendBridge
import CompPoly.Univariate.ToPoly.Impl

namespace AspisR1.CompPolySplitTrial
open CompPoly AspisR1.CompPolyPolynomialBackendBridge

def proper {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (d f : CPolynomial K) : Bool := !(d == 1) && !(d == f)

/-- No field enumeration or dense X^q appears in this executable trial. -/
def trySplit {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f h : CPolynomial K) (q : Nat) : Option (CPolynomial K) :=
  let d0 := CPolynomial.gcdMonic f h
  if proper d0 f then some d0 else
    let d1 := CPolynomial.gcdMonic f (modPower h f (q/2) - 1)
    if proper d1 f then some d1 else none

def linear {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (c : K × K) : CPolynomial K :=
  CPolynomial.C c.1 + CPolynomial.C c.2 * CPolynomial.X

def failure {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (f : CPolynomial K) (q : Nat) (c : K × K) : Rat :=
  if (trySplit f (linear c) q).isSome then 0 else 1

noncomputable section
open Polynomial AspisR1.CantorZassenhausSplit AspisR1.CantorZassenhausFastTrial
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem proper_iff (d f : CPolynomial K) :
    proper d f = true ↔ d.toPoly ≠ 1 ∧ d.toPoly ≠ f.toPoly := by
  have heq (p q : CPolynomial K) : p = q ↔ p.toPoly = q.toPoly :=
    by
      constructor
      · exact congrArg CPolynomial.toPoly
      · intro h
        apply CPolynomial.ringEquiv.injective
        simpa only [CPolynomial.ringEquiv_apply] using h
  simp [proper, heq, CPolynomial.toPoly_one]

theorem trial_success_iff (f h : CPolynomial K) (q : Nat)
    (hf : f.toPoly.Monic) :
    (trySplit f h q).isSome = true ↔ FastTrialSuccess f.toPoly h.toPoly q := by
  have hp0 : proper (CPolynomial.gcdMonic f h) f = true ↔
      ProperFactor (monicGCD f.toPoly h.toPoly) f.toPoly := by
    rw [proper_iff, gcd_backend_correct]
    simp only [ProperFactor, monicGCD_dvd_left, true_and]
  have hp1 : proper (CPolynomial.gcdMonic f (modPower h f (q/2)-1)) f = true ↔
      ProperFactor (monicGCD f.toPoly (polynomialModPower h.toPoly f.toPoly (q/2)-1)) f.toPoly := by
    rw [proper_iff, gcd_backend_correct, CPolynomial.toPoly_sub,
      modPower_backend_correct h f hf, CPolynomial.toPoly_one]
    simp only [ProperFactor, monicGCD_dvd_left, true_and]
  unfold trySplit FastTrialSuccess
  dsimp only
  split
  · rename_i h0
    exact iff_of_true rfl (Or.inl (hp0.mp h0))
  · rename_i h0
    split
    · rename_i h1
      exact iff_of_true rfl (Or.inr (hp1.mp h1))
    · rename_i h1
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_or]
      exact ⟨fun h => h0 (hp0.mpr h), fun h => h1 (hp1.mpr h)⟩

theorem linear_toPoly (c : K × K) : (linear c).toPoly = randomLinear c := by
  simp only [linear, randomLinear, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly]

theorem failure_eq_math (f : CPolynomial K) (q : Nat) (c : K × K)
    (hf : f.toPoly.Monic) : failure f q c = fastFailure f.toPoly q c := by
  have h := trial_success_iff f (linear c) q hf
  rw [linear_toPoly] at h
  simp only [failure, fastFailure]
  by_cases hs : FastTrialSuccess f.toPoly (randomLinear c) q
  · simp only [h.mpr hs, ↓reduceIte, hs]
  · have hn : ¬ (trySplit f (linear c) q).isSome = true := fun ht => hs (h.mp ht)
    simp only [hn, ↓reduceIte, hs, Bool.false_eq_true]

theorem actual_trial_failure_le_half (f : CPolynomial K) (a b : K) (q : Nat)
    (hq : q = Fintype.card K) (hf : f.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < degree f.toPoly) (hab : a ≠ b)
    (hodd : ringChar K ≠ 2) (ha : IsRoot f.toPoly a) (hb : IsRoot f.toPoly b) :
    (∑ c : K × K, failure f q c) / ((q : Rat)^2) ≤ 1/2 := by
  simp_rw [failure_eq_math f q _ hf]
  exact linear_fast_trial_failure_le_half f.toPoly a b q hq hf hdeg hab hodd ha hb

#print axioms proper_iff
#print axioms trial_success_iff
#print axioms failure_eq_math
#print axioms actual_trial_failure_le_half
end
end AspisR1.CompPolySplitTrial
