import CompPolyFactorTwoChildBound
import CompPolySplitStateClosure

noncomputable section
namespace AspisR1.CompPolyFactorAbortBound
open CompPoly Polynomial
open AspisR1.CompPolyFactorOracleProgram AspisR1.CompPolyFactorMeanTools
open AspisR1.CompPolySplitRetries AspisR1.CompPolySplitStateClosure
open AspisR1.CompPolySplitFactorQuality AspisR1.CompPolyFactorTwoChildBound
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.AdaptiveFirstReadLaw
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem retry_mean_le (f : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hf : SplitState f) (hdeg : 1 < f.toPoly.natDegree) :
    mean (fun tape : Fin t → K × K => retryFailure f q t tape) ≤ (1/2)^t := by
  obtain ⟨a,b,hab,ha,hb⟩ := two_distinct_roots f hf hdeg
  have hpos : (0 : WithBot Nat) < f.toPoly.degree := by
    rw [Polynomial.degree_eq_natDegree hf.1.ne_zero]
    exact_mod_cast (show 0 < f.toPoly.natDegree by omega)
  have hcard : (Fintype.card (Fin t → K × K) : ℚ) = ((q : ℚ)^2)^t := by
    rw [hq]
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_mul, pow_two]
  unfold mean
  rw [hcard]
  exact actual_retry_failure_le f a b q t hq hf.1 hpos hab hodd ha hb

/-- Global failure bound in the existing independent-answer interpreter.
Inputs at later nodes are allowed to depend on earlier answers. This theorem
includes every retry and child abort and proves fuel sufficiency from degree.
Connecting the independently sampled interpreter to fixed random heap tapes
still needs the separate freshness/no-reuse law. -/
theorem independent_factor_abort_le (q t : Nat) (fuel node : Nat)
    (f : CPolynomial K) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hf : SplitState f) (hFuel : f.toPoly.natDegree < fuel) :
    outMean (factorProgram q t fuel node f) abortIndicator ≤
      ((f.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  induction fuel generalizing node f with
  | zero => omega
  | succ fuel ih =>
    rw [factorProgram]
    split
    · change (0 : ℚ) ≤ _
      positivity
    · rename_i hzero
      split
      · change (0 : ℚ) ≤ _
        positivity
      · rename_i hone
        have hlarge : 1 < f.toPoly.natDegree := by
          rw [← CPolynomial.natDegree_toPoly]
          omega
        have heps : (0 : ℚ) ≤ (1/2)^t := by positivity
        let B : ℚ := ((f.toPoly.natDegree-2 : Nat) : ℚ) * (1/2)^t
        have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) heps
        have hpoint : ∀ tape : Fin t → K × K,
          outMean (match retry f q t tape with
            | none => .done none
            | some d =>
              bind (factorProgram q t fuel (2*node+1) d) (fun left =>
                match left with
                | none => .done none
                | some l =>
                  bind (factorProgram q t fuel (2*node+2) (f.divByMonic d)) (fun right =>
                    match right with
                    | none => .done none
                    | some r => .done (some (l++r))))) abortIndicator ≤
              retryFailure f q t tape+B := by
          intro tape
          cases hd : retry f q t tape with
          | none =>
            change (1 : ℚ) ≤ retryFailure f q t tape+B
            simp only [retryFailure, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            exact le_add_of_nonneg_right hB
          | some d =>
            have hqf := retry_quality f d q t tape hf.1 hd
            have hc := complement_quality f d hf.1 hqf.1 hqf.2
            dsimp only at hc
            have hstates := retry_children_state f d q t tape hf hd
            have hlfuel : d.toPoly.natDegree < fuel := by omega
            have hrfuel : (f.divByMonic d).toPoly.natDegree < fuel := by omega
            have hl := ih (2*node+1) d hstates.1 hlfuel
            have hr := ih (2*node+2) (f.divByMonic d) hstates.2 hrfuel
            have hsum : (d.toPoly.natDegree-1) + ((f.divByMonic d).toPoly.natDegree-1) =
                f.toPoly.natDegree-2 := by
              have hadd : d.toPoly.natDegree + (f.divByMonic d).toPoly.natDegree =
                  f.toPoly.natDegree := by
                rw [← Polynomial.natDegree_mul hqf.1.ne_zero hc.2.1.ne_zero, hc.1]
              omega
            simp only [retryFailure, hd, Option.isSome_some, ↓reduceIte, zero_add]
            calc
              _ ≤ ((d.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t +
                  (((f.divByMonic d).toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t :=
                two_children_abort_le
                  (factorProgram q t fuel (2*node+1) d)
                  (factorProgram q t fuel (2*node+2) (f.divByMonic d))
                  _ _ (mul_nonneg (Nat.cast_nonneg _) heps) hl hr
              _ = B := by
                rw [← add_mul, ← Nat.cast_add, hsum]
        change mean (fun tape => outMean _ abortIndicator) ≤ _
        calc
          _ ≤ mean (fun tape => retryFailure f q t tape+B) := FS.mean_mono hpoint
          _ = mean (fun tape => retryFailure f q t tape)+B := by
            rw [FS.mean_add, mean_const]
          _ ≤ (1/2)^t+B := add_le_add (retry_mean_le f q t hq hodd hf hlarge) (le_refl B)
          _ = ((f.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
            have hn : f.toPoly.natDegree-1 = 1+(f.toPoly.natDegree-2) := by omega
            rw [hn]
            dsimp only [B]
            push_cast
            ring

#print axioms retry_mean_le
#print axioms independent_factor_abort_le
end AspisR1.CompPolyFactorAbortBound
