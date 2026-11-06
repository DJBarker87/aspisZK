import NKU_DigestProofFrame
import NKU_DigestPublicFrame
import NKU_DigestCheckpointFrame
import NKU_DigestJoin
set_option autoImplicit false
noncomputable section
namespace NKU_DigestState
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem preserved {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) («end» : Usize) :
 NKU_Core.Preserves (NKU_DigestJoin.run d hash «end») :=
 NKU_Core.bind _ _ (NKU_DigestProofFrame.preserved d hash)
  (NKU_Core.bind _ _ (NKU_DigestPublicFrame.preserved d hash) (NKU_DigestCheckpointFrame.preserved d hash «end»))
#print axioms preserved
end NKU_DigestState
