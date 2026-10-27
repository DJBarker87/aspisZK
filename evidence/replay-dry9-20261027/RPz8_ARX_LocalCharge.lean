import RPz8_ARX_Cap
import RPz7_P2P_Charge
import RPz8_F3U_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_LocalCharge
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The recorder is a continuation of precisely the source view. -/
theorem congr_source {X : Type} (p q : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) (same : eval H p = eval H q) :
    eval H (Hiq_RecordedJoint.program p project select) =
      eval H (Hiq_RecordedJoint.program q project select) := by
  simp only [Hiq_RecordedJoint.program,Hist_JointCharge.joint,Hist_AuditQueries.augmented,
    SdkC_Replay.augmented,eval_bind,OracleProgramRecording.eval_record,same]

def bounded {X : Type} (source : Program Bytes State X) (Q : Nat) : Program Bytes State X :=
  ARX_Cap.cap (Q+1921) (eval (fun _ => SelectedTranscriptParams.params.iv) source).2 source

theorem budget {X : Type} (source : Program Bytes State X) (Q : Nat) (H : Bytes → State) :
    (eval H (bounded source Q)).1.length ≤ Q+1921 := ARX_Cap.length ..

theorem exact {X : Type} (source : Program Bytes State X) (Q : Nat) (H : Bytes → State)
    (bound : (eval H source).1.length ≤ Q+1921) : eval H (bounded source Q) = eval H source :=
  ARX_Cap.exact _ _ _ _ bound

theorem binding {X : Type} (source : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (H : Bytes → State) (bound : (eval H source).1.length ≤ Q+1921) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) ∨
    R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2 := by
  have same := exact source Q H bound
  have result := P2P_Charge.binding_or_collision (bounded source Q) project select Q
    (fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (budget source Q K)) H
  rw [congr_source _ _ project select H same,same] at result
  exact result

theorem canonical {X : Type} (source : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (H : Bytes → State) (bound : (eval H source).1.length ≤ Q+1921)
    (collision : AuS1_Finish.Collision H (eval H source).1
      (project (eval H source).2).1 (project (eval H source).2).2) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) := by
  have same := exact source Q H bound
  have result := F3U_AccountEvent.charged (bounded source Q) project select Q
    (fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (budget source Q K)) H
    (by rw [same]; exact collision)
  rw [congr_source _ _ project select H same] at result
  exact result

#print axioms congr_source
#print axioms budget
#print axioms exact
#print axioms binding
#print axioms canonical
end AspisR1.ARX_LocalCharge
end
