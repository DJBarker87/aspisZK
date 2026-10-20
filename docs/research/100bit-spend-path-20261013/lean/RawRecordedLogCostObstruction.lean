import RawExtractorCostComposedV2
import RawCutRecordedWordsExecutable

/-! Instrument the actual first-occurrence scan without changing its value.
A stored true acceptance flag does not bound the scan's input length.
The last theorem is conditional on scan adequacy: it does not assert that
all extractor branches demand a particular cut. -/
namespace AspisR1.RawRecordedLogCostObstruction
open RawExtractorCostComposedV2 RawCutProverCompiler
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Each inspected log entry costs one read, including the matching entry. -/
def firstIndexWithReads {I A : Type} [DecidableEq I] (a : I) :
    List (I × A) → Nat × Nat
  | [] => (0, 0)
  | (i, _) :: rest =>
    if i = a then (0, 1) else
      let r := firstIndexWithReads a rest
      (r.1 + 1, r.2 + 1)

theorem firstIndexWithReads_value {I A : Type} [DecidableEq I]
    (a : I) (tr : List (I × A)) :
    (firstIndexWithReads a tr).1 =
      RawCutRecordedWordsExecutable.firstIndexExec a tr := by
  induction tr with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨i, v⟩
    by_cases h : i = a <;>
      simp only [firstIndexWithReads, RawCutRecordedWordsExecutable.firstIndexExec,
        h, ite_true, ite_false, ih]

theorem firstIndexWithReads_le_length {I A : Type} [DecidableEq I]
    (a : I) (tr : List (I × A)) :
    (firstIndexWithReads a tr).2 ≤ tr.length := by
  induction tr with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
    rcases entry with ⟨i, v⟩
    by_cases h : i = a
    · simp only [firstIndexWithReads, h, ite_true, List.length_cons]
      omega
    · simpa only [firstIndexWithReads, h, ite_false, List.length_cons]
        using Nat.add_le_add_right ih 1

/-- Same recursion as cutBeforeExec; copying the prefix is not charged here. -/
def cutBeforeWithReads (tr : List (Bytes × State)) (frame : Bytes) :
    List (Bytes × State) × Nat :=
  let r := firstIndexWithReads frame tr
  (tr.take r.1, r.2)

theorem cutBeforeWithReads_value (tr : List (Bytes × State)) (frame : Bytes) :
    (cutBeforeWithReads tr frame).1 =
      RawCutRecordedWordsExecutable.cutBeforeExec tr frame := by
  simp only [cutBeforeWithReads, RawCutRecordedWordsExecutable.cutBeforeExec,
    firstIndexWithReads_value]

theorem firstIndexWithReads_replicate {I A : Type} [DecidableEq I]
    (a i : I) (v : A) (h : i ≠ a) (m : Nat) :
    firstIndexWithReads a (List.replicate m (i, v)) = (m, m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, firstIndexWithReads, h, ite_false, ih]

/-- No validity/reachability is asserted: this tests precisely the domain of
LedgerRefinement, whose only run restriction is the stored acceptance flag. -/
theorem accepted_log_unbounded (seed : RunView) (bound : Nat) :
    ∃ run : RunView, run.2.2 = true ∧ bound < run.1.length := by
  refine ⟨(List.replicate (bound + 1) ([], default), (seed.2.1, true)), rfl, ?_⟩
  simp only [List.length_replicate]
  omega

/-- The actual scan primitive has unbounded read counts on that same domain.
Use a symbolic repeated log, never reduce a large concrete list. -/
theorem accepted_cut_unbounded (seed : RunView) (frame : Bytes) (bound : Nat) :
    ∃ run : RunView, run.2.2 = true ∧
      bound < (cutBeforeWithReads run.1 frame).2 := by
  have hne : frame ++ [0] ≠ frame := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hl
    omega
  refine ⟨(List.replicate (bound + 1) (frame ++ [0], default),
    (seed.2.1, true)), rfl, ?_⟩
  simp only [cutBeforeWithReads, firstIndexWithReads_replicate _ _ _ hne]
  omega

/-- Any proposed fixed-parameter ledger covering this demanded scan on all
accepted-tagged views is contradictory. This is an explicit adequacy premise,
not a claimed full-extractor lower bound on parse/retry abort branches. -/
theorem no_ledger_of_universal_cut_adequacy
    (seed : RunView) (coins : Coins) (frame : Bytes)
    (e : CostedExtractor) (p : Parameters)
    (hscan : ∀ run : RunView, run.2.2 = true →
      (cutBeforeWithReads run.1 frame).2 ≤ (e.eval run coins).2.logReads) :
    ¬ LedgerRefinement e p := by
  intro hledger
  obtain ⟨run, ha, hbig⟩ := accepted_cut_unbounded seed frame p.readBudget
  have hsmall := (hscan run ha).trans (hledger.reads run coins ha)
  omega

#print axioms firstIndexWithReads_value
#print axioms firstIndexWithReads_le_length
#print axioms cutBeforeWithReads_value
#print axioms firstIndexWithReads_replicate
#print axioms accepted_log_unbounded
#print axioms accepted_cut_unbounded
#print axioms no_ledger_of_universal_cut_adequacy
end AspisR1.RawRecordedLogCostObstruction
