import CompPolySplitFactorQuality

namespace AspisR1.CompPolyFactorRecursion
open CompPoly AspisR1.CompPolySplitRetries

/-- A bounded binary factorization tree. Each node has its own retry tape.
No enumeration fallback is present: insufficient fuel or failed retries abort.
Tapes at heap indices 2*i+1 and 2*i+2 are reserved for the two children. -/
def factor {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (q t : Nat) (coins : Nat → Fin t → K × K) :
    Nat → Nat → CPolynomial K → Option (List K)
  | 0, _, _ => none
  | fuel+1, node, f =>
      if f.natDegree = 0 then some [] else
      if f.natDegree = 1 then some [-f.coeff 0] else
      match retry f q t (coins node) with
      | none => none
      | some d =>
        match factor q t coins fuel (2*node+1) d with
        | none => none
        | some left =>
          match factor q t coins fuel (2*node+2) (f.divByMonic d) with
          | none => none
          | some right => some (left ++ right)

noncomputable section
open Polynomial AspisR1.CompPolySplitFactorQuality
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

/-- Every successful execution returns a complete linear-factor certificate
for that exact input, independently of its random tape values. -/
theorem factor_product (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) (roots : List K)
    (hf : f.toPoly.Monic) (hs : factor q t coins fuel node f = some roots) :
    (roots.map (fun a => (X - C a : K[X]))).prod = f.toPoly := by
  induction fuel generalizing node f roots with
  | zero => simp [factor] at hs
  | succ fuel ih =>
    rw [factor] at hs
    split at hs
    · rename_i hzero
      cases hs
      have hn : f.toPoly.natDegree = 0 := (CPolynomial.natDegree_toPoly f).symm.trans hzero
      simpa only [List.map_nil, List.prod_nil] using (hf.natDegree_eq_zero.mp hn).symm
    · split at hs
      · rename_i hone
        cases hs
        have hn : f.toPoly.natDegree = 1 := (CPolynomial.natDegree_toPoly f).symm.trans hone
        have hlin := hf.eq_X_add_C hn
        simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
          C_neg, sub_neg_eq_add, CPolynomial.coeff_toPoly] using hlin.symm
      · cases hd : retry f q t (coins node) with
        | none => simp [hd] at hs
        | some d =>
          rw [hd] at hs
          dsimp only at hs
          have hquality := retry_quality f d q t (coins node) hf hd
          have hc := complement_quality f d hf hquality.1 hquality.2
          dsimp only at hc
          cases hl : factor q t coins fuel (2*node+1) d with
          | none => simp [hl] at hs
          | some left =>
            rw [hl] at hs
            dsimp only at hs
            cases hr : factor q t coins fuel (2*node+2) (f.divByMonic d) with
            | none => simp [hr] at hs
            | some right =>
              rw [hr] at hs
              dsimp only at hs
              cases hs
              rw [List.map_append, List.prod_append,
                ih (2*node+1) d left hquality.1 hl,
                ih (2*node+2) (f.divByMonic d) right hc.2.1 hr]
              exact hc.1

#print axioms factor
#print axioms factor_product
end
end AspisR1.CompPolyFactorRecursion
