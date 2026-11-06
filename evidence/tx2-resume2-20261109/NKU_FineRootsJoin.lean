import NKU_Fold
import NKU_FineGammaJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineRootsJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.roots d s=NKU_BodyJoin.run d s := by
 simp only [NKU_Fold.roots,NKU_BodyJoin.run,NKU_FineRoots.installed,NKU_FineGammaJoin.installed]
#print axioms installed
end NKU_FineRootsJoin
