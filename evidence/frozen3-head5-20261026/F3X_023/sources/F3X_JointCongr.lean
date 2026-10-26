import Hiq_RecordedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_JointCongr
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem evaluation {A : Type} (left right : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) (same : eval H left=eval H right) :
    eval H (Hiq_RecordedJoint.program left project select)=
      eval H (Hiq_RecordedJoint.program right project select) := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,
    SdkC_Replay.augmented,OracleProgramRecording.eval_record,eval_bind,eval]
  rw [same]

#print axioms evaluation
end AspisR1.F3X_JointCongr
end
