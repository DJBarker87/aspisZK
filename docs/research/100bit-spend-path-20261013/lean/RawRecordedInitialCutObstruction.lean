import RawRecordedLogCostObstruction
import RawCommitmentFrameReplay

/-! Specialize the scan counterexample to the exact initial commitment frame
used by wordsFromRun, preserving the public statement and proof of a seed.
This does not claim that every branch evaluates a received word. -/
namespace AspisR1.RawRecordedInitialCutObstruction
open RawRecordedLogCostObstruction RawCutProverCompiler RawExtractorCostComposedV2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem initial_frame_log_independent (run seed : RunView)
    (h : run.2.1 = seed.2.1) :
    RawCommitmentFrameReplay.frameFromView run 0 =
      RawCommitmentFrameReplay.frameFromView seed 0 := by
  change RawCommitmentFrameReplay.frameAt run.2.1.1
      RawCommitmentFrameReplay.zeroState 0 (run.2.1.2 0) =
    RawCommitmentFrameReplay.frameAt seed.2.1.1
      RawCommitmentFrameReplay.zeroState 0 (seed.2.1.2 0)
  rw [h]

/-- Same public and proof; only the unrestricted log and acceptance bit change.
The absent initial frame forces exactly bound+1 inspections if demanded. -/
theorem accepted_initial_cut_unbounded (seed : RunView) (bound : Nat) :
    ∃ run : RunView, run.2.1 = seed.2.1 ∧ run.2.2 = true ∧
      bound < (cutBeforeWithReads run.1
        (RawCommitmentFrameReplay.frameFromView run 0)).2 := by
  let frame := RawCommitmentFrameReplay.frameFromView seed 0
  let run : RunView :=
    (List.replicate (bound+1) (frame ++ [0], default), (seed.2.1, true))
  have hne : frame ++ [0] ≠ frame := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hl
    omega
  refine ⟨run, rfl, rfl, ?_⟩
  rw [initial_frame_log_independent run seed rfl]
  change bound < (cutBeforeWithReads
    (List.replicate (bound+1) (frame ++ [0], default)) frame).2
  simp only [cutBeforeWithReads, firstIndexWithReads_replicate _ _ _ hne]
  omega

theorem no_ledger_of_initial_cut_adequacy
    (seed : RunView) (coins : Coins) (e : CostedExtractor) (p : Parameters)
    (hscan : ∀ run : RunView, run.2.2 = true →
      (cutBeforeWithReads run.1 (RawCommitmentFrameReplay.frameFromView run 0)).2 ≤
        (e.eval run coins).2.logReads) :
    ¬ LedgerRefinement e p := by
  intro hledger
  obtain ⟨run, _, ha, hbig⟩ := accepted_initial_cut_unbounded seed p.readBudget
  have hsmall := (hscan run ha).trans (hledger.reads run coins ha)
  omega

/-- A size-restricted caller can use the old read polynomial for these scans.
Neither the size premise nor the caller-count premise follows from acceptance. -/
theorem bounded_cut_batch (tr : List (Bytes × State)) (frames : List Bytes)
    (n q : Nat) (hlog : tr.length ≤ q) (hcalls : frames.length ≤ 7*n) :
    (frames.map (fun frame => (cutBeforeWithReads tr frame).2)).sum ≤ 7*n*q := by
  apply RawExtractorCostLedger.sum_charge_le frames _ (7*n) q hcalls
  intro frame _
  exact (firstIndexWithReads_le_length frame tr).trans hlog

#print axioms initial_frame_log_independent
#print axioms accepted_initial_cut_unbounded
#print axioms no_ledger_of_initial_cut_adequacy
#print axioms bounded_cut_batch
end AspisR1.RawRecordedInitialCutObstruction
