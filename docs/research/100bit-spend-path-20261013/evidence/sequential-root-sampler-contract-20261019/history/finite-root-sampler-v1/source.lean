import CompPolySequentialRootsContract
import SequentialFiniteTapeLaw

namespace AspisR1.CompPolyFiniteRootSampler
open CompPoly AspisR1.CompPolySequentialAbortBound
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleFiniteSupport

/-- A concrete finite random-tape input. This definition is executable and
has no field-enumeration fallback. Every tape entry is t pairs of field values. -/
def runFromFiniteTape {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q t : Nat)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K) :
    Option (List K) × Nat :=
  (eval (extend (Finset.range (p.natDegree-1)) H (fun _ => (0,0)))
    (rootsProgram p q t)).2

noncomputable section
open Polynomial AspisV8PairedCommitment
open AspisR1.CompPolySequentialRootsContract AspisR1.CompPolyFactorMeanTools
open AspisR1.SequentialProgramInvariants AspisR1.SequentialFiniteTapeLaw
open AspisR1.CompPolyCompleteRoots AspisR1.CompPolyFactorOracleProgram
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem finite_sampler_correct (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly.Monic)
    (hdeg : (0 : WithBot Nat) < p.toPoly.degree)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K) :
    RootResult p (runFromFiniteTape p q t H) :=
  rootsProgram_eval_correct p q t hq hp hdeg _

/-- A finite uniform input tape gives the already proved adaptive abort
bound for this executable runner. Uniformity of an actual bit sampler is a
separate refinement obligation, not a hidden premise of correctness. -/
theorem finite_sampler_abort_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (hp : p.toPoly.Monic) (hdeg : (0 : WithBot Nat) < p.toPoly.degree) :
    mean (fun H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K =>
      abortIndicator (runFromFiniteTape p q t H).1) ≤
      ((p.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  have hend : AllOutcomes (rootsProgram p q t) (fun out => out.2 ≤ p.natDegree-1) :=
    all_mono _ (rootsProgram_correct p q t hq hp hdeg) (fun out ho => by
      simpa only [CPolynomial.natDegree_toPoly] using ho.1)
  have he := sequential_finite_tape_law
    (factorProgram q t (p.natDegree+1) 0 (rootFactor p q)) 0 (p.natDegree-1)
    hend (fun _ => ((0 : K),0)) (fun out => abortIndicator out.1)
  change mean (fun H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K =>
      abortIndicator (runFromFiniteTape p q t H).1) =
      lazyMean (rootsProgram p q t) (fun _ => none) (fun v => abortIndicator v.2.1) at he
  rw [he]
  simpa only [CPolynomial.natDegree_toPoly] using
    rootsProgram_abort_le p q t hq hodd hp hdeg

#print axioms runFromFiniteTape
#print axioms finite_sampler_correct
#print axioms finite_sampler_abort_le
end
end AspisR1.CompPolyFiniteRootSampler
