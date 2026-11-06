import NKU_Fold
import NKU_FineFirstJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineGammaJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.gamma d s=NKU_GammaJoin.run d s := by
 simp only [NKU_Fold.gamma,NKU_GammaJoin.run,NKU_FineGamma.installed,NKU_FineFirstJoin.installed,NKU_QueryJoin.run]
#print axioms installed
end NKU_FineGammaJoin
