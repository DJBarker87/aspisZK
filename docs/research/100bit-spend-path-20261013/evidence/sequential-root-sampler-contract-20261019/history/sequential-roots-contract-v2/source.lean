import CompPolySequentialFactorInvariant
import CompPolySequentialAbortBound

noncomputable section
namespace AspisR1.CompPolySequentialRootsContract
open CompPoly Polynomial AspisR1.CompPolyFactorCertificate
open AspisR1.CompPolyCompleteRoots AspisR1.CompPolySequentialAbortBound
open AspisR1.CompPolySequentialFactorInvariant
open AspisR1.SequentialFreshProgram AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def RootResult (p : CPolynomial K) (out : Option (List K) × Nat) : Prop :=
  out.2 ≤ p.toPoly.natDegree-1 ∧
    ∀ roots, out.1 = some roots →
      (∀ x, IsRoot p.toPoly x ↔ x ∈ roots) ∧
        roots.Nodup ∧ roots.length ≤ p.toPoly.natDegree

/-- All successful results enumerate precisely the distinct roots, and every
branch, including failure, consumes at most degree(p)-1 fresh tape blocks. -/
theorem rootsProgram_correct (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree) :
    AllOutcomes (rootsProgram p q t) (RootResult p) := by
  have hb := rootFactor_backend_correct p q hp
  have hm : (rootFactor p q).toPoly.Monic := by
    rw [hb]
    exact FiniteFieldNormalizedRootFactor.rootFactor_monic _ _ hp.ne_zero
  have hle : (rootFactor p q).toPoly.natDegree ≤ p.toPoly.natDegree := by
    rw [hb]
    exact Polynomial.natDegree_le_of_dvd
      (FiniteFieldNormalizedRootFactor.rootFactor_dvd _ _) hp.ne_zero
  apply all_mono _ (sequential_factor_invariant q t (p.natDegree+1) 0 0
    (rootFactor p q) hm)
  intro out hout
  refine ⟨?_, ?_⟩
  · exact hout.1.trans (by omega)
  · intro roots hs
    have hprod : linearProduct roots = (rootFactor p q).toPoly := hout.2 roots hs
    have hsep : (linearProduct roots).Separable := by
      rw [hprod, hb]
      exact FiniteFieldNormalizedRootFactor.rootFactor_separable _ _ hq hp hdeg
    have hn : (roots : Multiset K).Nodup :=
      Polynomial.nodup_of_separable_prod (by simpa [linearProduct] using hsep)
    refine ⟨?_, hn, ?_⟩
    · intro x
      rw [← linearProduct_root_iff roots x, hprod, hb]
      exact (FiniteFieldNormalizedRootFactor.rootFactor_roots_iff _ _ hq hp hdeg x).symm
    · have hlen := (linearProduct_monic_degree roots).2
      rw [hprod] at hlen
      omega

theorem rootsProgram_eval_correct (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree) (H : Nat → Fin t → K × K) :
    RootResult p (eval H (rootsProgram p q t)).2 :=
  all_eval H _ _ (rootsProgram_correct p q t hq hp hdeg)

/-- The sample budget bounds the actual query trace, without a successful-run
condition or any distributional assumption on H. Each answer has t field pairs. -/
theorem rootsProgram_trace_bound (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree) (H : Nat → Fin t → K × K) :
    (eval H (rootsProgram p q t)).1.length ≤ p.toPoly.natDegree-1 := by
  have hc := rootsProgram_eval_correct p q t hq hp hdeg H
  have he := sequential_eval_cursor H
    (AspisR1.CompPolyFactorOracleProgram.factorProgram q t (p.natDegree+1) 0 (rootFactor p q)) 0
  change (eval H (rootsProgram p q t)).2.2 =
    0 + (eval H (rootsProgram p q t)).1.length at he
  rw [he] at hc
  simpa only [Nat.zero_add] using hc.1

/-- Correctness, the consumption budget and the abort bound refer to one
program. The probability is the existing independent uniform field-tape law. -/
theorem rootsProgram_contract (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hp : p.toPoly.Monic) (hdeg : (0 : WithBot Nat) < p.toPoly.degree) :
    AllOutcomes (rootsProgram p q t) (RootResult p) ∧
      lazyMean (rootsProgram p q t) (fun _ => none)
        (fun v => AspisR1.CompPolyFactorMeanTools.abortIndicator v.2.1) ≤
        ((p.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t :=
  ⟨rootsProgram_correct p q t hq hp hdeg,
    rootsProgram_abort_le p q t hq hodd hp hdeg⟩

#print axioms RootResult
#print axioms rootsProgram_correct
#print axioms rootsProgram_eval_correct
#print axioms rootsProgram_trace_bound
#print axioms rootsProgram_contract
end AspisR1.CompPolySequentialRootsContract
