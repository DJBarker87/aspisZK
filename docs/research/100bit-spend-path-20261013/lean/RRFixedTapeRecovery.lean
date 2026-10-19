import RRConcreteRawRecovery

set_option autoImplicit false
namespace AspisR1.RRFixedTapeRecovery
open CompPoly Polynomial RRVectorRowPolynomialBridge RRDenseCoeffVector
open AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteInitialValidStateFromFacts
open AspisR1.RRConcreteTraversal AspisR1.RRConcreteTraversalLaw
open AspisR1.RRProgramRecoveryContracts AspisR1.RRConcreteRetryBudget
open AspisR1.CompPolyFactorMeanTools
open AspisR1.SequentialProgramInvariants AspisR1.SequentialFreshProgram
open AspisR1.SequentialFiniteTapeLaw
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport AspisV8PairedCommitment

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- The public tape bound depends only on the depth and row-degree limit,
not on the polynomial produced by interpolation or its normalization. -/
def recover (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (d * ell)} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  (eval (extend (Finset.range (d * ell)) H (fun _ => (0, 0)))
    (sequential (run ell q t d (initialValidState ell s hd hn)) 0)).2

theorem recover_correct [Fintype K] (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (d * ell)} → Fin t → K × K)
    (candidates : List (List K))
    (hs : (recover ell q t d s hd hn H).1 = some candidates) :
    CandidateResult model d s candidates := by
  have hc := all_eval (extend (Finset.range (d * ell)) H (fun _ => (0, 0))) _ _
    (all_sequential _ _ (run_recovery ell q t d (initialValidState ell s hd hn) hq) 0)
  have hr := hc candidates hs
  have hroots := initialValidState_roots ell s hd hn
  constructor
  · intro candidate hmem
    exact (hroots (toPolynomial candidate)).mp (hr.1 candidate hmem)
  · intro f hf hbound
    exact hr.2 f ((hroots f).mpr hf) hbound

theorem run_end_bound [Fintype K] (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K) :
    AllOutcomes (sequential (run ell q t d (initialValidState ell s hd hn)) 0)
      (fun out => out.2 ≤ d * ell) := by
  apply all_mono _ (run_sequential_end_bound ell q t d
    (initialValidState ell s hd hn) hq 0)
  intro out hout
  apply hout.trans
  simpa only [Nat.zero_add] using
    Nat.mul_le_mul_left d (mass_le_ell ell (initialValidState ell s hd hn))

theorem recover_cursor_le [Fintype K] (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (d * ell)} → Fin t → K × K) :
    (recover ell q t d s hd hn H).2 ≤ d * ell :=
  all_eval (extend (Finset.range (d * ell)) H (fun _ => (0, 0))) _ _
    (run_end_bound ell q t d s hd hn hq)

noncomputable section
variable [Fintype K]

/-- Exact uniform law on a public fixed-size tape. Interpolation may choose
any valid raw polynomial independently of this tape. -/
theorem recover_abort_le (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (d * ell)} → Fin t → K × K =>
      abortIndicator (recover ell q t d s hd hn H).1) ≤
      (d : ℚ) * (ell : ℚ) * (1/2)^t := by
  unfold recover
  rw [sequential_finite_tape_law (run ell q t d (initialValidState ell s hd hn))
    0 (d * ell) (run_end_bound ell q t d s hd hn hq)
    (fun _ => (0, 0)) (fun out => abortIndicator out.1)]
  apply le_trans (run_sequential_abort_le ell q t d (initialValidState ell s hd hn)
    hq hodd 0 (fun _ => none) (fun _ _ => rfl))
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast mass_le_ell ell (initialValidState ell s hd hn)

#print axioms recover
#print axioms recover_correct
#print axioms run_end_bound
#print axioms recover_cursor_le
#print axioms recover_abort_le
end
end AspisR1.RRFixedTapeRecovery
