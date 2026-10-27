import XRl_CheckpointBytes
open Aeneas Aeneas.Std Result
namespace XRl_CheckpointFinalizer
/-- Isolated final checked conversion fragment of XRk's checkpoint model.
The whole-body statement in L097 timed out and is NOT inferred here. -/
theorem size (out : List U8) (n : Nat) (bytes : Slice U8)
    (run : (if out.length=n then XRk_asSlice out else fail .panic)=ok bytes) :
    bytes.val.length=n := by
  split at run
  · rename_i checked
    unfold XRk_asSlice at run
    split at run
    · have actual := congrArg (fun s : Slice U8 => s.val.length) (Result.ok.inj run)
      exact actual.symm.trans checked
    · cases run
  · cases run
#print axioms size
end XRl_CheckpointFinalizer
