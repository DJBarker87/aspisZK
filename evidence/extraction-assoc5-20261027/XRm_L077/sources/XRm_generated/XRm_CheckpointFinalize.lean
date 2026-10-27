import XRm_CheckpointLayout
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRm_CheckpointFinalize
/-- Isolated final guard, avoiding reduction of the whole serialized prefix. -/
def finish (bs : List U8) (checksum : Array U8 32#usize) (size : Nat) : Result (alloc.vec.Vec U8) :=
  if (bs++checksum.val).length=size then XRk_asSlice (bs++checksum.val) else fail .panic
theorem value (bs : List U8) (checksum : Array U8 32#usize) (size : Nat)
    (out : alloc.vec.Vec U8) (run : finish bs checksum size=ok out) :
    out.val=bs++checksum.val := by
  unfold finish at run
  split_ifs at run
  · exact XRm_CheckpointCalls.slice _ _ run
#print axioms value
end XRm_CheckpointFinalize
