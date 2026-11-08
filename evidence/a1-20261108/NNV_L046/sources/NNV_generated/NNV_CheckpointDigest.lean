import NNV_PreparedAtHost
import LIBC_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CheckpointDigest
open Aeneas Aeneas.Std Result NNH_Run5bCtx
/-- Exact partitioned bytes and reply, with digest VALUE left at runtime trust. -/
theorem source {W Tx : Type} (c : Ctx W Tx) (parts : Slice (Slice U8)) :
 (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)).digest () parts =
 (LIBC_Checkpoint.digest (envOf c)).digest () parts := rfl
#print axioms source
end AspisR1.NNV_CheckpointDigest
end
