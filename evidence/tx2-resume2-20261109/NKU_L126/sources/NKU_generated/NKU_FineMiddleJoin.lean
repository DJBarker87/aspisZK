import NKU_Fold
import NKU_FineLastJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineMiddleJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.middleQuery d s=NKU_QueryMiddleJoin.run d s := by
 simp only [NKU_Fold.middleQuery,NKU_QueryMiddleJoin.run,NKU_FineQueryMid.installed,NKU_FineLastJoin.installed]
#print axioms installed
end NKU_FineMiddleJoin
