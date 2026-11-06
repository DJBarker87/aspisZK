import NKU_Fold
set_option autoImplicit false
noncomputable section
namespace NKU_FineZJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.z d s=NKU_ZJoin.run d s := by
 simp only [NKU_Fold.z,NKU_ZJoin.run,NKU_FineZ.installed]
#print axioms installed
end NKU_FineZJoin
