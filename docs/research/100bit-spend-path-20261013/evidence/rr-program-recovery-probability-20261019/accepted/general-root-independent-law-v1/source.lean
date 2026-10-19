import CompPolyGeneralRootsProgram

noncomputable section
namespace AspisR1.CompPolyGeneralRootIndependentLaw
open CompPoly AspisR1.CompPolyGeneralRootsProgram
open AspisR1.SequentialFreshProgram AspisR1.CompPolyFactorMeanTools
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8PairedCommitment
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem generalRoots_fresh_empty (p : CPolynomial K) (q t : Nat) :
    FreshFrom (generalRootsProgram p q t) (fun _ => none) := by
  rw [generalRootsProgram]
  split
  · trivial
  · split
    · trivial
    · exact sequential_fresh _ 0 (fun _ => none) (fun _ _ => rfl)

/-- The local root call has the same abort bound in the independent-answer
interpreter used for composing adaptively selected RR child programs. -/
theorem generalRoots_independent_abort_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) (hp : p.toPoly ≠ 0) :
    outMean (generalRootsProgram p q t) (fun out => abortIndicator out.1) ≤
      ((p.toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  have h := generalRoots_abort_le p q t hq hodd hp
  rw [lazyMean_eq_independentMean _ _ (generalRoots_fresh_empty p q t)] at h
  exact h

#print axioms generalRoots_fresh_empty
#print axioms generalRoots_independent_abort_le
end AspisR1.CompPolyGeneralRootIndependentLaw
