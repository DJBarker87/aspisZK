import SdkD_FirstModel
import SdkD_SecondModel
import SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_BatchUnion
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted (H : Bytes → State) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (first : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).2 = true)
    (second : (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch1)).2 = true) :
    (eval H (SdkC_Replay.replay p q)).2 = true := by
  rw [SdkC_Replay.replay,OraclePortFrozen2.batches]
  simp only [eval_bind,first,ite_true,second]

#print axioms accepted
end AspisR1.SdkD_BatchUnion
end
