import NKU_Fold
import NKU_FineMiddleJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineFirstJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.firstQuery d s=NKU_QueryFirstJoin.run d s := by
 simp only [NKU_Fold.firstQuery,NKU_QueryFirstJoin.run,NKU_FineQueryFirst.installed,NKU_FineMiddleJoin.installed]
#print axioms installed
end NKU_FineFirstJoin
