import RRConcreteTraversal
import SequentialFiniteTapeLaw

namespace AspisR1.RRConcreteTraversalLaw
open CompPoly Polynomial
open AspisR1.RRConcreteTraversal AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRProgramAbortBound AspisR1.RRProgramQueryBound
open AspisR1.CompPolyFactorMeanTools AspisR1.CompPolyGeneralRootQueryCost
open AspisR1.ProgramQueryCost AspisR1.SequentialProgramInvariants
open AspisR1.SequentialFreshProgram AspisR1.SequentialFiniteTapeLaw
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport AspisV8PairedCommitment
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

/-- Fixed finite input implementation of the whole concrete traversal. -/
def runFromFiniteTape (ell q t d : Nat) (s : ValidState ell K)
    (H : {i : Nat // i ∈ Finset.range (d * mass ell s)} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  (eval (extend (Finset.range (d * mass ell s)) H (fun _ => (0,0)))
    (sequential (run ell q t d s) 0)).2

noncomputable section
variable [Fintype K]

theorem children_abort_le (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    outMean (children ell s q t) abortIndicator ≤ (mass ell s : ℚ) * (1/2)^t := by
  have hn : (scalarPolynomial s.val).toPoly.natDegree-1 ≤ mass ell s := by
    change (scalarPolynomial s.val).toPoly.natDegree-1 ≤ (scalarPolynomial s.val).natDegree
    rw [CPolynomial.natDegree_toPoly]
    exact Nat.sub_le _ _
  calc
    _ = outMean (AspisR1.RRConcreteChildrenProgram.childrenProgram ell s.val q t)
        abortIndicator := by
      rw [children, AspisR1.RRConcreteChildrenProgram.childrenProgram,
        outMean_bind, outMean_bind]
      apply outMean_congr
      intro out
      cases h : out.1 <;> rfl
    _ ≤ (((scalarPolynomial s.val).toPoly.natDegree-1 : Nat) : ℚ) * (1/2)^t :=
      AspisR1.RRConcreteChildrenProgram.childrenProgram_abort_le ell s.val q t hq hodd
        (scalar_nonzero ell s)
    _ ≤ (mass ell s : ℚ) * (1/2)^t :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)

theorem children_cost_mass (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) :
    AllCosts (children ell s q t) (fun _ n => n ≤ mass ell s) := by
  unfold children
  apply allCosts_bind
  apply allCosts_mono _ (generalRootsProgram_cost_le (scalarPolynomial s.val) q t hq
    (scalar_nonzero ell s))
  intro out n hn
  change n+0 ≤ mass ell s
  apply hn.trans
  change (scalarPolynomial s.val).toPoly.natDegree-1 ≤ (scalarPolynomial s.val).natDegree
  rw [CPolynomial.natDegree_toPoly]
  exact Nat.sub_le _ _

theorem children_cost_and_mass (ell : Nat) (s : ValidState ell K) (q t : Nat)
    (hq : q = Fintype.card K) :
    AllCosts (children ell s q t) (fun out n => n ≤ mass ell s ∧
      ∀ cs, out = some cs → childMass (mass ell) cs ≤ mass ell s) :=
  allCosts_and _ (children_cost_mass ell s q t hq)
    (allCosts_of_all _ _ (children_mass ell s q t hq))

theorem run_abort_le (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    outMean (run ell q t d s) abortIndicator ≤
      (d : ℚ) * (mass ell s : ℚ) * (1/2)^t :=
  collectProgram_abort_le (fun u : ValidState ell K => zeroTest u.val) (fun s => children ell s q t)
    (mass ell) ((1/2)^t) (by positivity)
    (fun s => children_abort_le ell s q t hq hodd)
    (fun s => children_mass ell s q t hq) d s

theorem run_sequential_end_bound (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (cursor : Nat) :
    AllOutcomes (sequential (run ell q t d s) cursor)
      (fun out => out.2 ≤ cursor + d * mass ell s) :=
  collectProgram_sequential_end_bound (fun u : ValidState ell K => zeroTest u.val)
    (fun s => children ell s q t) (mass ell)
    (fun s => children_cost_and_mass ell s q t hq) d s cursor

theorem run_actual_trace_bound (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (cursor : Nat) (H : Nat → Fin t → K × K) :
    (eval H (sequential (run ell q t d s) cursor)).1.length ≤ d * mass ell s :=
  collectProgram_actual_trace_bound (fun u : ValidState ell K => zeroTest u.val)
    (fun s => children ell s q t) (mass ell)
    (fun s => children_cost_and_mass ell s q t hq) d s cursor H

theorem run_sequential_abort_le (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2)
    (cursor : Nat) (table : Table Nat (Fin t → K × K))
    (hfuture : ∀ i, cursor ≤ i → table i = none) :
    lazyMean (sequential (run ell q t d s) cursor) table
      (fun v => abortIndicator v.2.1) ≤
      (d : ℚ) * (mass ell s : ℚ) * (1/2)^t := by
  rw [sequential_lazy_mean _ _ _ hfuture]
  exact run_abort_le ell q t d s hq hodd

/-- The complete concrete traversal uses a finite input tape of at most d*m
blocks, each containing t field pairs. This is the independent uniform-field
law; conversion from bounded random bits to these field pairs is separate. -/
theorem run_finite_abort_le (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    mean (fun H : {i : Nat // i ∈ Finset.range (d * mass ell s)} → Fin t → K × K =>
      abortIndicator (eval (extend (Finset.range (d * mass ell s)) H
        (fun _ => (0,0))) (sequential (run ell q t d s) 0)).2.1) ≤
      (d : ℚ) * (mass ell s : ℚ) * (1/2)^t := by
  have hend : AllOutcomes (sequential (run ell q t d s) 0)
      (fun out => out.2 ≤ d * mass ell s) := by
    simpa only [Nat.zero_add] using run_sequential_end_bound ell q t d s hq 0
  rw [sequential_finite_tape_law (run ell q t d s) 0 (d * mass ell s)
    hend (fun _ => (0,0)) (fun out => abortIndicator out.1)]
  exact run_sequential_abort_le ell q t d s hq hodd 0 (fun _ => none) (fun _ _ => rfl)

theorem runFromFiniteTape_correct (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (d * mass ell s)} → Fin t → K × K)
    (candidates : List (List K))
    (hs : (runFromFiniteTape ell q t d s H).1 = some candidates) :
    AspisR1.RRProgramRecoveryContracts.CandidateResult
      (fun u : ValidState ell K => model u.val) d s candidates := by
  have hc := all_eval (extend (Finset.range (d * mass ell s)) H (fun _ => (0,0))) _ _
    (all_sequential _ _ (run_recovery ell q t d s hq) 0)
  exact hc candidates hs

#print axioms runFromFiniteTape
#print axioms runFromFiniteTape_correct
#print axioms children_abort_le
#print axioms children_cost_mass
#print axioms children_cost_and_mass
#print axioms run_abort_le
#print axioms run_sequential_end_bound
#print axioms run_actual_trace_bound
#print axioms run_sequential_abort_le
#print axioms run_finite_abort_le
end
end AspisR1.RRConcreteTraversalLaw
