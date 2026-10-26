import F3_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Decision
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local instance] Classical.propDecidable

/-- Only the value is transported. The physical-public checkpoint read
addresses in the two programs remain different. -/
theorem after_value (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) :
    (eval H (F3_Model.afterBatch0 physical stored p q tr)).2=
      (eval H (OraclePortFrozen2.afterBatch0 stored p q tr)).2 := by
  unfold F3_Model.afterBatch0 OraclePortFrozen2.afterBatch0
  split
  · simp only [eval_bind,F3_Model.checkpoint_value,OraclePortFrozen2.checkpoint_value]
  · rfl

theorem value (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) :
    (eval H (F3_Model.decision physical stored tr m)).2=
      (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).2 := by
  unfold F3_Model.decision OraclePortFrozen2.dV_frozen2
  split
  · split
    · simp only [eval_bind]
      split
      · exact after_value H physical stored _ _ tr
      · rfl
    · rfl
  · rfl

theorem admitted (physical : F3_Model.PhysicalPublic) (stored : Bytes) :
    OraclePortAdmission.admit (F3_Model.decision physical stored)=F3_Model.decision physical stored := by
  funext tr m
  unfold OraclePortAdmission.admit F3_Model.decision
  split <;> rfl

theorem accepted_details (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (tr : RawCutTranscriptRun.ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage)
    (H : Bytes → State) (accepted : (eval H (F3_Model.decision physical stored tr m)).2=true) :
    OraclePortAdmission.Guard tr ∧ ∃ p q i,
      OraclePortStoredParserC4.parseReached stored tr=some p ∧ queries tr=some q ∧
      (eval H (OraclePortShortCircuit.short (OraclePortBatchDraft.slotPrograms p q OraclePortFrozenOrder.slots))).2=true ∧
      input p q tr=some i ∧ D0TypedChecks.verify (typedRows p q tr) i=true :=
  OraclePortFrozen2.accepted_details stored tr m H ((value H physical stored tr m).symm.trans accepted)

#print axioms after_value
#print axioms value
#print axioms admitted
#print axioms accepted_details
end AspisR1.F3T_Decision
end
