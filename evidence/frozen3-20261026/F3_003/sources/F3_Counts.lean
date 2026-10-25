import F3_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3_Counts
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local instance] Classical.propDecidable

/-- All inputs, including rejection; raw P replaces U without adding a call. -/
theorem after_bound (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) :
    (eval H (F3_Model.afterBatch0 physical stored p q tr)).1.length ≤ 569 := by
  unfold F3_Model.afterBatch0
  split
  · rename_i i v hi hv
    simp only [eval_bind,F3_Model.checkpoint_value,OraclePortFrozen2.stage2,
      eval_bind,eval,List.append_nil,List.length_append]
    have hc := F3_Model.checkpoint_reads H physical stored p q tr i v
    have hb := OraclePortFrozen2.batch1_bound H p q
    omega
  · simp [eval]

theorem decision_budget (physical : F3_Model.PhysicalPublic) :
    OraclePortStoredExperimentC4.Budget (F3_Model.decision physical) := by
  intro stored H tr m
  unfold F3_Model.decision
  split
  · split
    · rename_i p q hp hq
      have before := OraclePortFrozen2.batch0_bound H p q
      have after := after_bound H physical stored p q tr
      simp only [eval_bind,List.length_append]
      cases hb : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2 <;>
        simp only [if_true,Bool.false_eq_true,if_false,eval,List.length_nil] <;> omega
    · simp [eval]
  · simp [eval]

/-- Checked complete-verifier envelope: 115 sampler + 477 batch0 + 6
checkpoint + 563 batch1 = 1161. Not an exact universal parent count. -/
theorem verifier_bound (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (i : F3_Model.Input) : (eval H (F3_Model.verifier D i)).1.length ≤ 1161 :=
  OraclePortStoredExperimentC4.verifier_budget D (F3_Model.decision i.physical)
    (decision_budget i.physical) H _

/-- Actual first-read bound for a single pass after an arbitrary F3 prover.
This does not assert the still-unbuilt frozen3 annotated extractor theorem. -/
theorem original_distinct (D : LiteralByteProtocol.Decoder)
    (P : Program Bytes State F3_Model.Input) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (bind P fun i => F3_Model.verifier D i)).1 ≤ Q+1161 := by
  rw [eval_bind]
  have reads := VerifierCallBudget.firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (F3_Model.verifier D (eval H P).2)).1)
  have hp := hq H
  have hv := verifier_bound D H (eval H P).2
  rw [List.length_append] at reads
  omega

#print axioms after_bound
#print axioms decision_budget
#print axioms verifier_bound
#print axioms original_distinct
end AspisR1.F3_Counts
end
