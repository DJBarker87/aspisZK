import RPx_Schedule
import RPx_Duplicates
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Checkpoint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

theorem duplicate_policy (H : Bytes → State) (stored pub : Bytes) (c : Context)
    (d : MatchingSupport.Data E) (rho : K) (q : Fin 22 → Fin 262144) :
    let address := OraclePortPhysicalFrameDraft.domain ++
      (save H stored pub c d rho q).checkpoint.take 1736
    let triple := [(stored,H stored),(pub,H pub),(address,H address)]
    RPx_Schedule.checkpointReads H stored pub c d rho q = triple++triple ∧
    (RPx_Schedule.checkpointReads H stored pub c d rho q).length=6 ∧
    FS.firstReads FS.emptyTable (RPx_Schedule.checkpointReads H stored pub c d rho q)=
      FS.firstReads FS.emptyTable triple := by
  dsimp only
  have shape : RPx_Schedule.checkpointReads H stored pub c d rho q =
      [(stored,H stored),(pub,H pub),
        (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736,
         H (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736))] ++
      [(stored,H stored),(pub,H pub),
        (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736,
         H (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736))] := rfl
  refine ⟨shape,rfl,?_⟩
  rw [shape]
  simpa only [List.nil_append] using OracleProgramRecording.firstReads_repeat_suffix []
    [(stored,H stored),(pub,H pub),
      (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736,
       H (OraclePortPhysicalFrameDraft.domain ++ (save H stored pub c d rho q).checkpoint.take 1736))]

#print axioms duplicate_policy
end AspisR1.RPx_Checkpoint
end
