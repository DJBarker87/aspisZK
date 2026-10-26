import RPz7_F3T_AccountCharge
import RPz7_Hiq_CanonicalEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AccountEvent
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound

theorem charged {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921)
    (H : Bytes → State)
    (collision : AuS1_Finish.Collision H (eval H source).1
      (project (eval H source).2).1 (project (eval H source).2).2) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) := by
  have included := Hiq_CanonicalEvent.source_to_joint source project select (Q+1921) budget H collision
  simpa only [Hiq_RecordedJoint.evaluation,BinRawByteCollisionTargets.event,Nat.add_assoc] using included

#print axioms charged
end AspisR1.F3U_AccountEvent
end
