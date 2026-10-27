import F3_Counts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3_CountInvariant
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local instance] Classical.propDecidable

theorem after_profile (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) :
    (eval H (F3_Model.afterBatch0 physical stored p q tr)).1.length =
      (eval H (OraclePortFrozen2.afterBatch0 stored p q tr)).1.length ∧
    (eval H (F3_Model.afterBatch0 physical stored p q tr)).2 =
      (eval H (OraclePortFrozen2.afterBatch0 stored p q tr)).2 := by
  cases hi : input p q tr <;> cases hv : LiteralOpeningView.read (typedRows p q tr) <;>
    simp only [F3_Model.afterBatch0,OraclePortFrozen2.afterBatch0,hi,hv,eval_bind,
      F3_Model.checkpoint_value,OraclePortFrozen2.checkpoint_value,
      OraclePortFrozen2.stage2,eval_bind,eval,List.append_nil,List.length_append,
      F3_Model.checkpoint_reads,OraclePortFrozen2.checkpoint_reads,and_self]

theorem decision_profile (H : Bytes → State) (physical : F3_Model.PhysicalPublic)
    (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) :
    (eval H (F3_Model.decision physical stored tr m)).1.length =
      (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.length ∧
    (eval H (F3_Model.decision physical stored tr m)).2 =
      (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).2 := by
  by_cases guard : OraclePortAdmission.Guard tr
  · cases hp : OraclePortStoredParserC4.parseReached stored tr with
    | none => simp only [F3_Model.decision,OraclePortFrozen2.dV_frozen2,if_pos guard,hp,eval,and_self]
    | some p =>
      cases hq : queries tr with
      | none => simp only [F3_Model.decision,OraclePortFrozen2.dV_frozen2,if_pos guard,hp,hq,eval,and_self]
      | some q =>
        have a := after_profile H physical stored p q tr
        simp only [F3_Model.decision,OraclePortFrozen2.dV_frozen2,if_pos guard,hp,hq,eval_bind]
        cases hb : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2 <;>
          simp only [Bool.false_eq_true,if_false,if_true,eval,List.length_append,
            a.1,a.2,and_self]
  · simp only [F3_Model.decision,OraclePortFrozen2.dV_frozen2,if_neg guard,eval,and_self]

/-- Exact all-input issued-call count equality, not oracle-address equality.
This cannot transport collision probabilities or recovered-input agreement. -/
theorem complete_count (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (i : F3_Model.Input) :
    (eval H (F3_Model.verifier D i)).1.length =
      (eval H (OraclePortStoredExperimentC4.verifier D OraclePortFrozen2.dV_frozen2
        ⟨i.semantic.value,i.proof,i.stored⟩)).1.length := by
  have profile := decision_profile H i.physical i.stored
    (LiteralTranscript.erasePrefix
      ((LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33))
    (LiteralTranscript.erase (i.proof 33))
  simpa only [F3_Model.verifier,OraclePortStoredExperimentC4.verifier,
    OraclePortExperiment.verifier,OracleDecisionFeasibilityBudget.verifier_eval,
    OracleDecisionFeasibilityCore.onBytes,List.length_append] using
    congrArg (fun n =>
      (((List.range 33).map fun j => (eval H
        ((LiteralByteProtocol.protocol D).chain H i.semantic.value i.proof j).toProgram).1).flatten).length + n)
      profile.1

#print axioms after_profile
#print axioms decision_profile
#print axioms complete_count
end AspisR1.F3_CountInvariant
end
