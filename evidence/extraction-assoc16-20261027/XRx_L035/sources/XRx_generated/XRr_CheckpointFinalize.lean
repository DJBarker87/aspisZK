import XRr_CheckpointLayout
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_CheckpointFinalize
/-- Symbolic guard: serialized prefix is an opaque list parameter. -/
def finish (bs : List U8) (checksum : Array U8 32#usize) (size : Nat) : Result (alloc.vec.Vec U8) :=
 if (bs++checksum.val).length=size then XRn_Join_asSlice (bs++checksum.val) else fail .panic
theorem value (bs : List U8) (checksum : Array U8 32#usize) (size : Nat)
 (out : alloc.vec.Vec U8) (run : finish bs checksum size=ok out) : out.val=bs++checksum.val := by
 unfold finish at run
 split at run
 · exact XRr_CheckpointLayout.slice _ out run
 · cases run
theorem length (bs : List U8) (checksum : Array U8 32#usize) (size : Nat)
 (out : alloc.vec.Vec U8) (run : finish bs checksum size=ok out) : out.val.length=size := by
 have hv := value bs checksum size out run
 unfold finish at run
 split at run
 · rename_i hl
   rw [hv];exact hl
 · cases run
#print axioms value
#print axioms length
end XRr_CheckpointFinalize
