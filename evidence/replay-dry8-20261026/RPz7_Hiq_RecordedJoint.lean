import RPz7_Hiq_JointBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RecordedJoint
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def program {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    Program Bytes State (View Bytes State A) :=
  Hist_JointCharge.joint (OracleProgramRecording.record source) (fun v => project v.2) (fun v => select v.2)

/-- Source trace recording adds zero queries and keeps the full original view
as output. The appended replay and audit use that same source result. -/
theorem evaluation {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (H : Bytes → State) :
    eval H (program source project select) =
      ((eval H (Hist_JointCharge.joint source project select)).1,eval H source) := by
  simp only [program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,SdkC_Replay.augmented,
    OracleProgramRecording.eval_record,eval_bind,eval,List.append_nil,List.append_assoc]

theorem source_view {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (H : Bytes → State) :
    (eval H (program source project select)).2 = eval H source := by rw [evaluation]

#print axioms evaluation
#print axioms source_view
end AspisR1.Hiq_RecordedJoint
end
