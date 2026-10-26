import SCI_SameWorld
import F3X_Join
import SCH_RecorderProjection
import SCH_EventKnownSuffix
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCI_Projection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Expand the ACTUAL heterogeneous recorder, exposing the selected replay
and all four selected physical audit reads. No query/log identity is assumed. -/
theorem recorder_log {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    (eval H (Hiq_RecordedJoint.program source project select)).1 =
      (eval H source).1 ++
      (eval H (SdkC_Replay.replay (project (eval H source).2).1
        (project (eval H source).2).2)).1 ++
      (eval H (Hist_AuditQueries.audit (select (eval H source).2).1
        (select (eval H source).2).2)).1 := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,
    Hist_AuditQueries.augmented,SdkC_Replay.augmented,
    OracleProgramRecording.eval_record,eval_bind,eval,List.append_nil,List.append_assoc]

/-- An equality of recorder logs necessarily identifies the LAST physical
public audit input. Sharing one oracle world alone cannot imply this. -/
theorem final_audit {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    (eval H (Hiq_RecordedJoint.program source project select)).1.getLast? =
      some ((select (eval H source).2).2.pub,H (select (eval H source).2).2.pub) := by
  rw [recorder_log,Hist_AuditQueries.audit_eval]
  simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.or_some]

/-- Concrete obstruction at the two requested recorder carriers: unequal
selected current-public audit bytes forbid ordered-log equality, regardless
of common H or of the earlier source/preparation/replay traces. This does
not claim that equal collision events require equal full logs. -/
theorem selected_audit_obstruction {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State)
    (prior : Program Bytes State Unit) (s : F3T_ByteCarrier.Submission)
    (lp : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (rp : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (rs : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (different : (lp (eval H (F3X_AccountPrior.program c hashv prior s)).2).2.pub ≠
      (rs (eval H (SCE_Experiment.account c hashv copy allocator id a)).2).2.pub) :
    (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
      F3X_Projection.project lp)).1 ≠
    (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account c hashv copy allocator id a)
      rp rs)).1 := by
  intro same
  have last := congrArg List.getLast? same
  rw [final_audit,final_audit] at last
  exact different (congrArg Prod.fst (Option.some.inj last))

/-- A sufficient exact identity for THESE concrete recorders, retaining each
unproved source/projection/selection equality explicitly. This is not the
unconditional requested event_eq and discharges no deployment premise. -/
theorem event_of_identified_projections {A F C : Type}
    (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State)
    (prior : Program Bytes State Unit) (s : F3T_ByteCarrier.Submission)
    (lp : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (rp : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (rs : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat)
    (source : (eval H (F3X_AccountPrior.program c hashv prior s)).1 =
      (eval H (SCE_Experiment.account c hashv copy allocator id a)).1)
    (projection : F3X_Projection.project (eval H (F3X_AccountPrior.program c hashv prior s)).2 =
      rp (eval H (SCE_Experiment.account c hashv copy allocator id a)).2)
    (selection : lp (eval H (F3X_AccountPrior.program c hashv prior s)).2 =
      rs (eval H (SCE_Experiment.account c hashv copy allocator id a)).2) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv Q
      (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
        F3X_Projection.project lp)) ↔
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv Q
      (eval H (Hiq_RecordedJoint.program (SCE_Experiment.account c hashv copy allocator id a) rp rs)) := by
  exact SCH_RecorderProjection.event _ _ _ _
    (SCH_RecorderProjection.logs _ _ _ _ _ _ H source projection selection)

#print axioms recorder_log
#print axioms final_audit
#print axioms selected_audit_obstruction
#print axioms event_of_identified_projections
end AspisR1.SCI_Projection
end
