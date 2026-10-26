import CompPolySplitFactorQuality

namespace AspisR1.CompPolyFactorSplitCount
open CompPoly AspisR1.CompPolySplitRetries

/-- Conservative count of splitting sites: it includes both child subtrees
even when the actual factorizer aborts before visiting the right child. -/
def splitSites {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (q t : Nat) (coins : Nat → Fin t → K × K) : Nat → Nat → CPolynomial K → Nat
  | 0, _, _ => 0
  | fuel+1, node, f =>
      if f.natDegree ≤ 1 then 0 else
      match retry f q t (coins node) with
      | none => 1
      | some d => 1 + splitSites q t coins fuel (2*node+1) d +
          splitSites q t coins fuel (2*node+2) (f.divByMonic d)

noncomputable section
open Polynomial AspisR1.CompPolySplitFactorQuality
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem splitSites_le_degree (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) (hf : f.toPoly.Monic) :
    splitSites q t coins fuel node f ≤ f.toPoly.natDegree - 1 := by
  induction fuel generalizing node f with
  | zero => simp [splitSites]
  | succ fuel ih =>
    rw [splitSites]
    split
    · exact Nat.zero_le _
    · rename_i hdegree
      have hlarge : 1 < f.toPoly.natDegree := by
        rw [← CPolynomial.natDegree_toPoly]
        omega
      cases hd : retry f q t (coins node) with
      | none => simp only; omega
      | some d =>
        dsimp only
        have hq := retry_quality f d q t (coins node) hf hd
        have hc := complement_quality f d hf hq.1 hq.2
        dsimp only at hc
        have hl := ih (2*node+1) d hq.1
        have hr := ih (2*node+2) (f.divByMonic d) hc.2.1
        have hsum : d.toPoly.natDegree + (f.divByMonic d).toPoly.natDegree =
            f.toPoly.natDegree := by
          rw [← Polynomial.natDegree_mul hq.1.ne_zero hc.2.1.ne_zero, hc.1]
        omega

#print axioms splitSites_le_degree
end
end AspisR1.CompPolyFactorSplitCount
