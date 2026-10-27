import Hiq_EventExtension
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_CanonicalEvent
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

theorem auth_to_replay {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) (H : Bytes → State) :
    EndP_AuthMass.event (eval H (EndP_AuthMass.program source project)) →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv
        (firstReads emptyTable (eval H source).1+1040)
        (eval H (SdkC_Replay.augmented source project)) := by
  simpa only [EndP_AuthMass.event,EndP_AuthMass.program,OracleProgramRecording.eval_record,
    SdkC_Replay.augmented,eval_bind,eval,List.append_nil,BinRawByteCollisionTargets.event]

/-- Actual canonical collision and history binding use one enlarged event.
The account source and all rejected prefixes precede both charged audits. -/
theorem source_to_joint {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State)
    (hit : AuS1_Finish.Collision H (eval H source).1 (project (eval H source).2).1 (project (eval H source).2).2) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+1044)
      (eval H (Hist_JointCharge.joint source project select)) := by
  have old := auth_to_replay source project H ((EndP_AuthMass.same_alternative source project H).mpr hit)
  exact Hiq_EventExtension.replay_to_joint source project select _ _ (by have b := budget H; omega) H old

#print axioms auth_to_replay
#print axioms source_to_joint
end AspisR1.Hiq_CanonicalEvent
end
