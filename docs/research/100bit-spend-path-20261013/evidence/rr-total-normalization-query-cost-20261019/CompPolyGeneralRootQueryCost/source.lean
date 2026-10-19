import ProgramQueryCost
import CompPolyGeneralRootsProgram

noncomputable section
namespace AspisR1.CompPolyGeneralRootQueryCost
open CompPoly Polynomial AspisR1.ProgramQueryCost
open AspisR1.CompPolyGeneralRootsProgram AspisR1.CompPolySequentialRootsContract
open AspisR1.CompPolySequentialAbortBound AspisR1.CompPolyFactorOracleProgram
open AspisV8R19.MemoizedProgramLaw
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

/-- Bounds actual ask count on every branch, including root-finder failures. -/
theorem rootsProgram_cost_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree) :
    AllCosts (rootsProgram p q t) (fun _ n => n ≤ p.toPoly.natDegree-1) := by
  have hcount := allCosts_sequential_cursor
    (factorProgram q t (p.natDegree+1) 0 (AspisR1.CompPolyCompleteRoots.rootFactor p q)) 0
  change AllCosts (rootsProgram p q t) (fun oc n => oc.2 = 0+n) at hcount
  have hcorrect := allCosts_of_all _ _ (rootsProgram_correct p q t hq hp hdeg)
  apply allCosts_mono _ (allCosts_and _ hcount hcorrect)
  intro out n ho
  have hc := ho.2.1
  omega

theorem generalRootsProgram_cost_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0) :
    AllCosts (generalRootsProgram p q t) (fun _ n => n ≤ p.toPoly.natDegree-1) := by
  have hz : ¬ (p == 0) = true := by
    intro h
    have he : p = 0 := LawfulBEq.eq_of_beq h
    exact hp (he ▸ CPolynomial.toPoly_zero)
  rw [generalRootsProgram, if_neg hz]
  by_cases hd : p.natDegree = 0
  · rw [if_pos hd]
    exact Nat.zero_le _
  · rw [if_neg hd]
    have hm : (CPolynomial.monicNormalize p).toPoly.Monic := by
      rw [CPolynomial.monicNormalize_toPoly_eq_normalize]
      exact Polynomial.monic_normalize hp
    have hdeg : (0 : WithBot Nat) < (CPolynomial.monicNormalize p).toPoly.degree := by
      rw [normalized_degree, Polynomial.degree_eq_natDegree hp]
      have hn : 0 < p.toPoly.natDegree := by
        rw [CPolynomial.natDegree_toPoly] at hd
        omega
      exact_mod_cast hn
    simpa only [normalized_natDegree] using
      rootsProgram_cost_le (CPolynomial.monicNormalize p) q t hq hm hdeg

#print axioms rootsProgram_cost_le
#print axioms generalRootsProgram_cost_le
end AspisR1.CompPolyGeneralRootQueryCost
