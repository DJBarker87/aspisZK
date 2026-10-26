import F3_Model
import OraclePortFrozen2Digests

/-! Adopted frozen3 schedule with physical checkpoint bytes and rejected prefixes.
Source-to-account accounting is proved separately; rejected log equality is not assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Schedule
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local irreducible] OraclePortCheckpointStateC3.advance OraclePortCheckpointStateC3.write
  QueryAccumulator.run QueryAccumulator.run22

def checkpointReads (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    List (Bytes × State) :=
  let address := OraclePortPhysicalFrameDraft.domain ++
    (save H stored pub c d rho q).checkpoint.take 1736
  [(stored,H stored),(pub,H pub),(address,H address),
   (stored,H stored),(pub,H pub),(address,H address)]

theorem checkpoint_eval (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View) :
    eval H (F3_Model.checkpoint physical stored p q tr i v) =
      (checkpointReads H stored physical.bytes
        (OraclePortAcceptedContextC6.context p i v) i.data
        (SelectedChallengeMap.rhoOf i.rho) q,
       some (OraclePortFrozen2.completeState i q)) := by
  apply Prod.ext
  · exact OraclePortFrozen2Digests.six_ordered_reads H stored physical.bytes
      (OraclePortAcceptedContextC6.context p i v) i.data
      (SelectedChallengeMap.rhoOf i.rho) q
  · exact F3_Model.checkpoint_value H physical stored p q tr i v

/-- The returned resumed state is used in finish, even when batch1 rejects.
Neither the six repeated reads nor a rejecting batch's prefix is erased. -/
theorem after_batch0 (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : SourceInputs) (v : LiteralOpeningView.View)
    (input : OraclePortStoredDecisionDraftC4.input p q tr = some i)
    (opening : LiteralOpeningView.read (typedRows p q tr) = some v) :
    eval H (F3_Model.afterBatch0 physical stored p q tr) =
      (checkpointReads H stored physical.bytes
          (OraclePortAcceptedContextC6.context p i v) i.data
          (SelectedChallengeMap.rhoOf i.rho) q ++
        (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1,
       (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2 &&
         OraclePortFrozen2.finish p q tr i (OraclePortFrozen2.completeState i q)) := by
  simp only [F3_Model.afterBatch0,input,opening,eval_bind,checkpoint_eval,
    OraclePortFrozen2.stage2,eval_bind,eval,List.append_nil]

/-- Complete decision normal form in the parsed/opening class; no acceptance
premise. Failed batch0 has exactly its own short-circuit log. Failed batch1
also retains the six checkpoint reads and its own short-circuit log. -/
theorem decision (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes) (p : Parsed)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) (i : SourceInputs) (v : LiteralOpeningView.View)
    (guard : OraclePortAdmission.Guard tr)
    (parsed : OraclePortStoredParserC4.parseReached stored tr = some p)
    (query : queries tr = some q)
    (input : OraclePortStoredDecisionDraftC4.input p q tr = some i)
    (opening : LiteralOpeningView.read (typedRows p q tr) = some v) :
    eval H (F3_Model.decision physical stored tr m) =
      let first := eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)
      let second := eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)
      if first.2 then
        (first.1 ++ (checkpointReads H stored physical.bytes
          (OraclePortAcceptedContextC6.context p i v) i.data
          (SelectedChallengeMap.rhoOf i.rho) q ++ second.1),
         second.2 && D0TypedChecks.verify (typedRows p q tr) i)
      else (first.1,false) := by
  simp only [F3_Model.decision,if_pos guard,parsed,query,eval_bind]
  cases first : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2
  · simp only [first,Bool.false_eq_true,if_false,eval,List.append_nil]
  · simp only [first,if_true,after_batch0 H physical stored p q tr i v input opening,
      OraclePortFrozen2.finish_value p q tr i input query]

#print axioms checkpoint_eval
#print axioms after_batch0
#print axioms decision
#print decision
end AspisR1.RPx_Schedule
end
