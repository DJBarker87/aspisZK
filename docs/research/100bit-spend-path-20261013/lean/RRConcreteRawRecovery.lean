import RRConcreteInitialValidStateFromFacts
import RRConcreteRetryBudget

set_option autoImplicit false
namespace AspisR1.RRConcreteRawRecovery
open CompPoly Polynomial RRVectorRowPolynomialBridge RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts
open AspisR1.RRConcreteTraversal AspisR1.RRConcreteTraversalLaw
open AspisR1.RRProgramRecoveryContracts AspisR1.RRConcreteRetryBudget
open AspisR1.CompPolyFactorMeanTools
open AspisR1.SequentialProgramInvariants AspisR1.SequentialFreshProgram
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport AspisV8PairedCommitment

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- Actual root recovery from raw rows, without a pre-normalized-state premise.
The two proof arguments are erased; normalization and traversal are executable. -/
def recover (ell q t d : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range
      (d * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  runFromFiniteTape ell q t d (initialValidState ell s hdegree hQ) H

theorem recover_correct [Fintype K] (ell q t d : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range
      (d * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K)
    (candidates : List (List K))
    (hs : (recover ell q t d s hdegree hQ H).1 = some candidates) :
    CandidateResult model d s candidates := by
  have hc := runFromFiniteTape_correct ell q t d (initialValidState ell s hdegree hQ)
    hq H candidates hs
  have hr := initialValidState_roots ell s hdegree hQ
  constructor
  · intro candidate hmem
    exact (hr (toPolynomial candidate)).mp (hc.1 candidate hmem)
  · intro f hf hbound
    exact hc.2 f ((hr f).mpr hf) hbound

theorem recover_cursor_le [Fintype K] (ell q t d : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range
      (d * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K) :
    (recover ell q t d s hdegree hQ H).2 ≤ d * ell := by
  have hc := all_eval (extend
      (Finset.range (d * mass ell (initialValidState ell s hdegree hQ))) H
      (fun _ => (0, 0))) _ _
    (run_sequential_end_bound ell q t d (initialValidState ell s hdegree hQ) hq 0)
  change (recover ell q t d s hdegree hQ H).2 ≤ _ at hc
  exact hc.trans (by simpa only [Nat.zero_add] using
    Nat.mul_le_mul_left d (mass_le_ell ell (initialValidState ell s hdegree hQ)))

noncomputable section
variable [Fintype K]

/-- The failure law is about the same executable finite-tape recovery above. -/
theorem recover_abort_le (ell q t d : Nat) (s : RawState K)
    (hdegree : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hQ : model s ≠ 0) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range
        (d * mass ell (initialValidState ell s hdegree hQ))} → Fin t → K × K =>
      abortIndicator (recover ell q t d s hdegree hQ H).1) ≤
      (d : ℚ) * (ell : ℚ) * (1/2)^t :=
  failureMass_le ell q t d (initialValidState ell s hdegree hQ) hq hodd

#print axioms recover
#print axioms recover_correct
#print axioms recover_cursor_le
#print axioms recover_abort_le
end
end AspisR1.RRConcreteRawRecovery
