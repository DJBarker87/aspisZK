import LPb_ResultInversion
open Aeneas Aeneas.Std Result
open XRk_Release
namespace LPb_CheckpointFinalValue
/-- Isolate both the byte list and size from the enclosing serializer. -/
def finish (bs : List U8) (sum : Array U8 32#usize) (size : Nat) : Result (alloc.vec.Vec U8) :=
  if (bs ++ sum.val).length = size then XRk_asSlice (bs ++ sum.val) else fail .panic

theorem finish_value (bs : List U8) (sum : Array U8 32#usize) (size : Nat)
    (out : alloc.vec.Vec U8) (run : finish bs sum size = ok out) :
    out.val = bs ++ sum.val := by
  unfold finish at run
  split_ifs at run
  · exact LPb_CheckpointLayout.slice_value (bs ++ sum.val) out run

theorem value (p : verifier.Prepared) (bs : List U8) (sum : Array U8 32#usize)
    (out : alloc.vec.Vec U8) (run : LPb_CheckpointSequence.lastStage p bs sum = ok out) :
    out.val = bs ++ sum.val :=
  finish_value bs sum (if p.variant matches .S1 then 4840 else 1768) out run
#print axioms finish_value
#print axioms value
end LPb_CheckpointFinalValue
