import NKU_FineRootsJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineDigestJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) (next : U8) («end» : Usize) :
 NKU_Fold.digest d hash s next «end»=NKU_DigestBody.run d hash s next «end» := by
 simp only [NKU_Fold.digest,NKU_DigestBody.run,NKU_FineRootsJoin.installed]
#print axioms installed
end NKU_FineDigestJoin
