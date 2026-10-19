import CompPolyFactorCounted
import CompPolySplitFactorQuality
import Lean.Elab.Tactic.Omega

/-! A call-graph cost mirror for the maintained bounded factorizer.  The
`charge` component is added exactly where the right recursive call evaluates
`f.divByMonic d`; the recursion and early-abort order follow `factor`.
The remaining raw-implementation bridge is isolated in `charge_le`.
-/
namespace AspisR1.CompPolyFactorTotalDivisionCost
open CompPoly AspisR1.CompPolySplitRetries AspisR1.CompPolyFactorRecursion
open AspisR1.CompPolySplitFactorQuality

def factorCosted {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (q t : Nat) (coins : Nat → Fin t → K × K)
    (charge : CPolynomial K → CPolynomial K → Nat) :
    Nat → Nat → CPolynomial K → Option (List K) × Nat
  | 0, _, _ => (none, 0)
  | fuel+1, node, f =>
      if f.natDegree = 0 then (some [], 0) else
      if f.natDegree = 1 then (some [-f.coeff 0], 0) else
      match retry f q t (coins node) with
      | none => (none, 0)
      | some d =>
        let left := factorCosted q t coins charge fuel (2*node+1) d
        match left.1 with
        | none => (none, left.2)
        | some l =>
          let division := charge f d
          let right := factorCosted q t coins charge fuel (2*node+2) (f.divByMonic d)
          match right.1 with
          | none => (none, left.2+division+right.2)
          | some r => (some (l++r), left.2+division+right.2)

theorem factorCosted_output (q t : Nat) (coins : Nat → Fin t → K × K)
    (charge : CPolynomial K → CPolynomial K → Nat)
    (fuel node : Nat) (f : CPolynomial K) :
    (factorCosted q t coins charge fuel node f).1 = factor q t coins fuel node f := by
  induction fuel generalizing node f with
  | zero => rfl
  | succ fuel ih =>
      simp only [factorCosted, factor]
      split
      · rfl
      · split
        · rfl
        · cases hd : retry f q t (coins node) with
          | none => rfl
          | some d =>
            dsimp only
            rw [ih]
            cases hl : factorCosted q t coins charge fuel (2*node+1) d with
            | mk lo lc =>
              cases lo with
              | none => rfl
              | some l =>
                dsimp only
                rw [ih]
                cases hr : factorCosted q t coins charge fuel
                    (2*node+2) (f.divByMonic d) with
                | mk ro rc => cases ro <;> rfl

private theorem combine_degree_budget (a b n B : Nat)
    (hsum : a+b=n) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a-1)*B + B + (b-1)*B = (n-1)*B := by
  have hn : a - 1 + 1 + (b - 1) = n - 1 := by omega
  calc
    (a-1)*B + B + (b-1)*B = ((a-1)+1+(b-1))*B := by
      rw [← Nat.one_mul B, ← Nat.add_mul, ← Nat.add_mul]
    _ = (n-1)*B := by rw [hn]

/-- If each actual recursive division site is charged at most `B`, then the
sum of those charges along the actual factor call graph is at most
`(degree-1)*B`. Degree additivity at an accepted split pays for the node's
own division plus both child trees; a failed left subtree skips the division
and right subtree exactly as the executable does.
-/
theorem factorCosted_total_le_degree_mul
    {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]
    (q t : Nat) (coins : Nat → Fin t → K × K)
    (charge : CPolynomial K → CPolynomial K → Nat) (B : Nat)
    (D : Nat)
    (hcharge : ∀ node f d, f.toPoly.Monic → f.toPoly.natDegree ≤ D →
      retry f q t (coins node) = some d →
      charge f d ≤ B)
    (fuel node : Nat) (f : CPolynomial K) (hf : f.toPoly.Monic)
    (hdeg : f.toPoly.natDegree ≤ D) :
    (factorCosted q t coins charge fuel node f).2 ≤
      (f.toPoly.natDegree - 1) * B := by
  induction fuel generalizing node f with
  | zero => simp [factorCosted]
  | succ fuel ih =>
      simp only [factorCosted]
      by_cases h0 : f.natDegree = 0
      · have hpoly0 : f.toPoly.natDegree = 0 :=
          (CPolynomial.natDegree_toPoly f).symm.trans h0
        simp [h0, hpoly0]
      by_cases h1 : f.natDegree = 1
      · have hpoly1 : f.toPoly.natDegree = 1 :=
          (CPolynomial.natDegree_toPoly f).symm.trans h1
        simp [h0, h1, hpoly1]
      simp only [h0, h1, ↓reduceIte]
      cases hd : retry f q t (coins node) with
      | none => simp [hd]
      | some d =>
          have hsplit := retry_quality f d q t (coins node) hf hd
          rcases complement_quality f d hf hsplit.1 hsplit.2 with
            ⟨hprod, heMonic, hdpos, hdlt, hepos, helt⟩
          have hdegree : d.toPoly.natDegree + (f.divByMonic d).toPoly.natDegree =
              f.toPoly.natDegree := by
            rw [← Polynomial.natDegree_mul hsplit.1.ne_zero heMonic.ne_zero, hprod]
          have hleft := ih (2*node+1) d hsplit.1 (Nat.le_trans (Nat.le_of_lt hdlt) hdeg)
          cases hl : factorCosted q t coins charge fuel (2*node+1) d with
          | mk l lc =>
            cases l with
            | none =>
                simp only [hl, Prod.fst, Prod.snd, ↓reduceIte]
                have hleftbound : lc ≤ (d.toPoly.natDegree-1)*B := by
                  simpa [hl] using hleft
                have hdegreeMono : (d.toPoly.natDegree-1)*B ≤
                    (f.toPoly.natDegree-1)*B :=
                  Nat.mul_le_mul_right B (Nat.sub_le_sub_right (Nat.le_of_lt hdlt) 1)
                exact hleftbound.trans hdegreeMono
            | some l =>
                have hright := ih (2*node+2) (f.divByMonic d) heMonic
                  (Nat.le_trans (Nat.le_of_lt helt) hdeg)
                cases hr : factorCosted q t coins charge fuel
                    (2*node+2) (f.divByMonic d) with
                | mk r rc =>
                    have hthis : charge f d ≤ B := hcharge node f d hf hdeg hd
                    have hsum := combine_degree_budget d.toPoly.natDegree
                      (f.divByMonic d).toPoly.natDegree f.toPoly.natDegree B
                      hdegree hdpos hepos
                    have hle1 : lc ≤ (d.toPoly.natDegree-1)*B := by
                      simpa [hl] using hleft
                    have hle2 : rc ≤ ((f.divByMonic d).toPoly.natDegree-1)*B := by
                      simpa [hr] using hright
                    cases r <;> simp only [hl, hr, Prod.fst, Prod.snd, ↓reduceIte] <;>
                      calc
                        _ ≤ (d.toPoly.natDegree-1)*B + B +
                            ((f.divByMonic d).toPoly.natDegree-1)*B := by omega
                        _ = (f.toPoly.natDegree-1)*B := hsum

#print axioms factorCosted_output
#print axioms factorCosted_total_le_degree_mul
end AspisR1.CompPolyFactorTotalDivisionCost
