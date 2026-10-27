import PFin_ReplayBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_ReplaySplit
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem log (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (first : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2=true) :
    (eval H (SdkC_Replay.replay p q)).1=
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1 ++
      (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).1 := by
  unfold SdkC_Replay.replay
  rw [OraclePortFrozen2.batches]
  simp only [eval_bind,first,if_true]

#print axioms log
end AspisR1.PFin_ReplaySplit
end
