import SequentialFreshProgram
import CompPolyFactorAbortBound
import CompPolyCompleteRoots

namespace AspisR1.CompPolySequentialAbortBound
open CompPoly AspisR1.CompPolyCompleteRoots AspisR1.CompPolyFactorOracleProgram
open AspisR1.SequentialFreshProgram
open AspisV8R19.MemoizedProgramLaw

/-- Fresh sequential-tape version of the root-finder program. -/
def rootsProgram {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q t : Nat) : Program Nat (Fin t → K × K) (Option (List K) × Nat) :=
  sequential (factorProgram q t (p.natDegree+1) 0 (rootFactor p q)) 0

noncomputable section
open Polynomial AspisV8PairedCommitment
open AspisR1.CompPolySplitStateClosure AspisR1.CompPolyFactorAbortBound
open AspisR1.CompPolyFactorMeanTools
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem sequential_factor_abort_le (q t fuel node cursor : Nat) (f : CPolynomial K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hf : SplitState f) (hFuel : f.toPoly.natDegree < fuel)
    (table : Table Nat (Fin t → K × K))
    (hfuture : ∀ i, cursor ≤ i → table i = none) :
    lazyMean (sequential (factorProgram q t fuel node f) cursor) table
      (fun v => abortIndicator v.2.1) ≤
      ((f.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  rw [sequential_lazy_mean _ _ _ hfuture]
  exact independent_factor_abort_le q t fuel node f hq hodd hf hFuel

theorem rootsProgram_abort_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hp : p.toPoly.Monic) (hdeg : (0 : WithBot Nat) < p.toPoly.degree) :
    lazyMean (rootsProgram p q t) (fun _ => none)
      (fun v => abortIndicator v.2.1) ≤
      ((p.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  have hb := rootFactor_backend_correct p q hp
  have hm : (rootFactor p q).toPoly.Monic := by
    rw [hb]
    exact FiniteFieldNormalizedRootFactor.rootFactor_monic _ _ hp.ne_zero
  have hsplit : SplitState (rootFactor p q) := by
    refine ⟨hm, ?_, ?_⟩ <;> rw [hb]
    · exact FiniteFieldNormalizedRootFactor.rootFactor_splits _ _ hq hp hdeg
    · exact FiniteFieldNormalizedRootFactor.rootFactor_separable _ _ hq hp hdeg
  have hle : (rootFactor p q).toPoly.natDegree ≤ p.toPoly.natDegree := by
    rw [hb]
    exact Polynomial.natDegree_le_of_dvd
      (FiniteFieldNormalizedRootFactor.rootFactor_dvd _ _) hp.ne_zero
  have hfuel : (rootFactor p q).toPoly.natDegree < p.natDegree+1 := by
    rw [CPolynomial.natDegree_toPoly]
    omega
  apply (sequential_factor_abort_le q t (p.natDegree+1) 0 0 (rootFactor p q)
    hq hodd hsplit hfuel (fun _ => none) (fun _ _ => rfl)).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.sub_le_sub_right hle 1

#print axioms rootsProgram
#print axioms sequential_factor_abort_le
#print axioms rootsProgram_abort_le
end
end AspisR1.CompPolySequentialAbortBound
