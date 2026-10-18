import CompPolyFactorRecursion
import CompPolyFactorSplitCount

namespace AspisR1.CompPolyFactorCounted
open CompPoly AspisR1.CompPolySplitRetries AspisR1.CompPolyFactorRecursion
open AspisR1.CompPolyFactorSplitCount

/-- Exact execution with a ghost counter incremented once for each retry
call. In particular a left-child abort skips the right child. -/
def factorCounted {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (q t : Nat) (coins : Nat → Fin t → K × K) :
    Nat → Nat → CPolynomial K → Option (List K) × Nat
  | 0, _, _ => (none, 0)
  | fuel+1, node, f =>
      if f.natDegree = 0 then (some [], 0) else
      if f.natDegree = 1 then (some [-f.coeff 0], 0) else
      match retry f q t (coins node) with
      | none => (none, 1)
      | some d =>
        let left := factorCounted q t coins fuel (2*node+1) d
        match left.1 with
        | none => (none, 1+left.2)
        | some l =>
          let right := factorCounted q t coins fuel (2*node+2) (f.divByMonic d)
          match right.1 with
          | none => (none, 1+left.2+right.2)
          | some r => (some (l++r), 1+left.2+right.2)

noncomputable section
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem factorCounted_refines (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) :
    (factorCounted q t coins fuel node f).1 = factor q t coins fuel node f := by
  induction fuel generalizing node f with
  | zero => rfl
  | succ fuel ih =>
    simp only [factorCounted, factor]
    split
    · rfl
    · split
      · rfl
      · cases hd : retry f q t (coins node) with
        | none => rfl
        | some d =>
          dsimp only
          rw [ih]
          cases hl : factor q t coins fuel (2*node+1) d with
          | none => rfl
          | some l =>
            dsimp only
            rw [ih]
            cases hr : factor q t coins fuel (2*node+2) (f.divByMonic d) <;> rfl

theorem factorCounted_le_splitSites (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) :
    (factorCounted q t coins fuel node f).2 ≤ splitSites q t coins fuel node f := by
  induction fuel generalizing node f with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    rw [factorCounted, splitSites]
    by_cases h0 : f.natDegree = 0
    · simp only [h0, Nat.zero_le, ↓reduceIte, Nat.le_refl]
    by_cases h1 : f.natDegree = 1
    · simp only [h0, h1, Nat.le_refl, Nat.one_ne_zero, ↓reduceIte]
    have hn : ¬ f.natDegree ≤ 1 := by omega
    simp only [h0, h1, hn, ↓reduceIte]
    cases hd : retry f q t (coins node) with
    | none => exact Nat.le_refl _
    | some d =>
      dsimp only
      have hl := ih (2*node+1) d
      have hr := ih (2*node+2) (f.divByMonic d)
      cases hc : (factorCounted q t coins fuel (2*node+1) d).1 with
      | none => dsimp only; omega
      | some l =>
        dsimp only
        cases he : (factorCounted q t coins fuel (2*node+2) (f.divByMonic d)).1 <;>
          dsimp only <;> omega

theorem actual_retry_calls_le_degree (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) (hf : f.toPoly.Monic) :
    (factorCounted q t coins fuel node f).2 ≤ f.toPoly.natDegree - 1 :=
  (factorCounted_le_splitSites q t coins fuel node f).trans
    (splitSites_le_degree q t coins fuel node f hf)

#print axioms factorCounted_refines
#print axioms factorCounted_le_splitSites
#print axioms actual_retry_calls_le_degree
end
end AspisR1.CompPolyFactorCounted
