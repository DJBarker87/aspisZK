import Hiq_RecordedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_Recorder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The recorder observes only the selected projections at the actual source
result. Both selector functions are fixed before H. -/
theorem select_congr {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (left right : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) (same : left (eval H source).2 = right (eval H source).2) :
    eval H (Hiq_RecordedJoint.program source project left) =
      eval H (Hiq_RecordedJoint.program source project right) := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,
    SdkC_Replay.augmented,OracleProgramRecording.eval_record,eval_bind,eval]
  rw [same]

#print axioms select_congr
end AspisR1.SCG_Recorder
end
