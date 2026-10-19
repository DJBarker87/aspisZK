import RRConcreteState
import CompPolyGeneralRootIndependentLaw
import RRProgramMeanTools
import CompPolyGeneralRootQueryCost

namespace AspisR1.RRConcreteChildrenProgram
open CompPoly AspisR1.RRConcreteState
open AspisR1.CompPolyGeneralRootsProgram
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- Executable normalization with a total fallback. For Valid parents the
finite scanner succeeds, so the fallback is unreachable. -/
def childRaw (ell : Nat) (s : RawState K) (a : K) : RawState K :=
  (normalizeChild? ell s a).getD s

def childList (ell : Nat) (s : RawState K) (roots : List K) :
    List (K × RawState K) := roots.map (fun a => (a, childRaw ell s a))

/-- The actual scalar root finder followed by deterministic row normalization.
The root finder's None remains None; no failed factorization becomes []. -/
def childrenProgram (ell : Nat) (s : RawState K) (q t : Nat) :
    Program Nat (Fin t → K × K) (Option (List (K × RawState K))) :=
  bind (generalRootsProgram (scalarPolynomial s) q t)
    (fun out => .done (out.1.map (childList ell s)))

noncomputable section
open AspisR1.SequentialProgramInvariants AspisR1.CompPolySequentialRootsContract
open AspisR1.CompPolyFactorMeanTools AspisR1.CompPolyGeneralRootIndependentLaw
open AspisV8PairedCommitment
variable [Fintype K]

theorem childrenProgram_correct (ell : Nat) (s : RawState K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : (scalarPolynomial s).toPoly ≠ 0) :
    AllOutcomes (childrenProgram ell s q t) (fun output =>
      ∃ sampled, RootResult (scalarPolynomial s) sampled ∧
        output = sampled.1.map (childList ell s)) := by
  unfold childrenProgram
  apply all_bind
  apply all_mono _ (generalRoots_correct (scalarPolynomial s) q t hq hp)
  intro sampled hs
  exact ⟨sampled, hs, rfl⟩

theorem childrenProgram_abort_le (ell : Nat) (s : RawState K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hp : (scalarPolynomial s).toPoly ≠ 0) :
    outMean (childrenProgram ell s q t) abortIndicator ≤
      (((scalarPolynomial s).toPoly.natDegree - 1 : Nat) : ℚ) * (1/2)^t := by
  rw [childrenProgram, outMean_bind]
  have heq :
      (fun out : Option (List K) × Nat =>
        outMean (Program.done (out.1.map (childList ell s)) :
          Program Nat (Fin t → K × K) _) abortIndicator) =
      (fun out => abortIndicator out.1) := by
    funext out
    cases h : out.1 <;> rfl
  rw [heq]
  exact generalRoots_independent_abort_le (scalarPolynomial s) q t hq hodd hp

theorem childrenProgram_cost_le (ell : Nat) (s : RawState K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : (scalarPolynomial s).toPoly ≠ 0) :
    AspisR1.ProgramQueryCost.AllCosts (childrenProgram ell s q t)
      (fun _ n => n ≤ (scalarPolynomial s).toPoly.natDegree-1) := by
  unfold childrenProgram
  apply AspisR1.ProgramQueryCost.allCosts_bind
  apply AspisR1.ProgramQueryCost.allCosts_mono _
    (AspisR1.CompPolyGeneralRootQueryCost.generalRootsProgram_cost_le
      (scalarPolynomial s) q t hq hp)
  intro out n hn
  exact hn

#print axioms childrenProgram_cost_le
#print axioms childRaw
#print axioms childList
#print axioms childrenProgram
#print axioms childrenProgram_correct
#print axioms childrenProgram_abort_le
end
end AspisR1.RRConcreteChildrenProgram
