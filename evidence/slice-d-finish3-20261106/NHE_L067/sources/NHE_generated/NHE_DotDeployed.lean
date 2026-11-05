import NHE_Dot
set_option autoImplicit false
namespace NHE_DotDeployed
open Aeneas Aeneas.Std Result AspisR1 NHE_DotBody

def stageResult : core.result.Result NE NHE_DotBody.Error →
 core.result.Result AspisR1Stage2.Stage2Finish.E AspisR1Stage2.verifier.Error
 | .Ok x=>.Ok (FIo_Install.fromE x)
 | .Err e=>.Err (SAG_DotAdapter.toStageError e)

theorem weights (ws : Slice NQ) :
 SAG_DotAdapter.mapSlice SAG_DotAdapter.toFinishQ (SAG_DotAdapter.mapSlice NHE_DotRead.stageQ ws)=
 SAG_DotAdapter.mapSlice NHE_DotRead.finishQ ws := by
 apply Subtype.ext
 simp only [SAG_DotAdapter.mapSlice,List.map_map,NHE_DotRead.finishQ]
 rfl

theorem cohort (bytes : Slice U8) (ws : Slice NQ) (size : ws.val.length≤64) :
 FIo_FieldBridge.map stageResult (NHE_Dot.source bytes ws)=
 SAG_DotClosed.source bytes (SAG_DotAdapter.mapSlice NHE_DotRead.stageQ ws) := by
 unfold SAG_DotClosed.source SAG_DotAdapter.sourceDot SAG_DotAdapter.kernel
 rw [weights,←NHE_Dot.cohort bytes ws size]
 cases run : NHE_Dot.source bytes ws with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

#print axioms weights
#print axioms cohort
end NHE_DotDeployed
