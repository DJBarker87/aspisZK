import RPz7_Hiq_RecordedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_RecorderProjection
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Heterogeneous recorder transport: outputs may have different carriers.
The conditions refer exactly to their actually selected projection and bytes. -/
theorem logs {A B : Type} (left : Program Bytes State A) (right : Program Bytes State B)
    (lp : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (rp : B → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (ls : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (rs : B → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State)
    (source : (eval H left).1 = (eval H right).1)
    (projection : lp (eval H left).2 = rp (eval H right).2)
    (selection : ls (eval H left).2 = rs (eval H right).2) :
    (eval H (Hiq_RecordedJoint.program left lp ls)).1 =
      (eval H (Hiq_RecordedJoint.program right rp rs)).1 := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,
    SdkC_Replay.augmented,OracleProgramRecording.eval_record,eval_bind,eval]
  rw [source,projection,selection]

/-- The collision event depends only on the recorded log, so output-carrier
identity is not an additional requirement. -/
theorem event {A B : Type} (iv : State) (Q : Nat)
    (left : View Bytes State A) (right : View Bytes State B)
    (same : left.1 = right.1) :
    BinRawByteCollisionTargets.event iv Q left ↔ BinRawByteCollisionTargets.event iv Q right := by
  unfold BinRawByteCollisionTargets.event
  rw [same]

#print axioms logs
#print axioms event
end AspisR1.SCH_RecorderProjection
end
