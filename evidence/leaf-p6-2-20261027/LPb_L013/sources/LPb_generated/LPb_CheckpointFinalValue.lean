import LPb_ResultInversion
open Aeneas Aeneas.Std Result
open XRk_Release
namespace LPb_CheckpointFinalValue
/-- Isolate the final guard on a symbolic byte list; never normalize payload. -/
theorem value (p : verifier.Prepared) (bs : List U8) (sum : Array U8 32#usize)
    (out : alloc.vec.Vec U8) (run : LPb_CheckpointSequence.lastStage p bs sum = ok out) :
    out.val = bs ++ sum.val := by
  unfold LPb_CheckpointSequence.lastStage at run
  split at run
  · exact LPb_CheckpointLayout.slice_value (bs ++ sum.val) out run
  · cases run
#print axioms value
end LPb_CheckpointFinalValue
