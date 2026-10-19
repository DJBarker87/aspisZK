import CompPolyGeneralRootsProgram

namespace AspisR1.CompPolyGeneralFiniteRootSampler
open CompPoly AspisR1.CompPolyGeneralRootsProgram
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleFiniteSupport

/-- Fixed finite input tape for arbitrary scalar input. The zero case
rejects without touching the tape; nonzero constants return no roots. -/
def runGeneralFromFiniteTape {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p : CPolynomial K) (q t : Nat)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K) :
    Option (List K) × Nat :=
  (eval (extend (Finset.range (p.natDegree-1)) H (fun _ => (0,0)))
    (generalRootsProgram p q t)).2

noncomputable section
open Polynomial AspisV8R19.OracleResampling AspisV8PairedCommitment
open AspisR1.SequentialProgramInvariants AspisR1.SequentialFreshProgram
open AspisR1.SequentialFiniteTapeLaw AspisR1.CompPolySequentialRootsContract
open AspisR1.CompPolyFactorMeanTools AspisR1.CompPolySequentialAbortBound
open AspisR1.CompPolyFactorOracleProgram AspisR1.CompPolyCompleteRoots
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

theorem general_cursor_eq_trace (p : CPolynomial K) (q t : Nat)
    (H : Nat → Fin t → K × K) :
    (eval H (generalRootsProgram p q t)).2.2 =
      (eval H (generalRootsProgram p q t)).1.length := by
  rw [generalRootsProgram]
  split
  · rfl
  · split
    · rfl
    · simpa only [rootsProgram, Nat.zero_add] using sequential_eval_cursor H
        (factorProgram q t ((CPolynomial.monicNormalize p).natDegree+1) 0
          (rootFactor (CPolynomial.monicNormalize p) q)) 0

theorem general_trace_bound (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0)
    (H : Nat → Fin t → K × K) :
    (eval H (generalRootsProgram p q t)).1.length ≤ p.toPoly.natDegree-1 := by
  have hc := (all_eval H _ _ (generalRoots_correct p q t hq hp)).1
  rw [general_cursor_eq_trace] at hc
  exact hc

theorem general_support_below (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0) :
    support (generalRootsProgram p q t) ⊆ Finset.range (p.natDegree-1) := by
  have hend : AllOutcomes (generalRootsProgram p q t)
      (fun out => out.2 ≤ p.natDegree-1) :=
    all_mono _ (generalRoots_correct p q t hq hp) (fun out ho => by
      simpa only [CPolynomial.natDegree_toPoly] using ho.1)
  unfold generalRootsProgram at hend ⊢
  by_cases hz : (p == 0) = true
  · rw [if_pos hz]
    exact Finset.empty_subset _
  · rw [if_neg hz] at hend ⊢
    by_cases hd : p.natDegree = 0
    · rw [if_pos hd]
      exact Finset.empty_subset _
    · rw [if_neg hd] at hend ⊢
      exact sequential_support_below _ 0 (p.natDegree-1) hend

theorem general_finite_correct (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hp : p.toPoly ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K) :
    RootResult p (runGeneralFromFiniteTape p q t H) :=
  all_eval _ _ _ (generalRoots_correct p q t hq hp)

theorem general_finite_abort_le (p : CPolynomial K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) (hp : p.toPoly ≠ 0) :
    mean (fun H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K =>
      abortIndicator (runGeneralFromFiniteTape p q t H).1) ≤
      ((p.natDegree-1 : Nat) : ℚ) * (1/2)^t := by
  have he := finite_support_oracle_law (generalRootsProgram p q t)
    (Finset.range (p.natDegree-1)) (general_support_below p q t hq hp)
    (fun _ => ((0 : K),0)) (fun v => abortIndicator v.2.1)
  change mean (fun H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K =>
      abortIndicator (runGeneralFromFiniteTape p q t H).1) =
      lazyMean (generalRootsProgram p q t) (fun _ => none)
        (fun v => abortIndicator v.2.1) at he
  rw [he]
  simpa only [CPolynomial.natDegree_toPoly] using generalRoots_abort_le p q t hq hodd hp

#print axioms runGeneralFromFiniteTape
#print axioms general_cursor_eq_trace
#print axioms general_trace_bound
#print axioms general_support_below
#print axioms general_finite_correct
#print axioms general_finite_abort_le
end
end AspisR1.CompPolyGeneralFiniteRootSampler
