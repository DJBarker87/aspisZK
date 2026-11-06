import NKU_Fold
import NKU_FineSemanticJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineLastJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.lastQuery d s=NKU_QueryLastJoin.run d s := by
 simp only [NKU_Fold.lastQuery,NKU_QueryLastJoin.run,NKU_FineQueryEnd.installed,NKU_FineSemanticJoin.installed]
#print axioms installed
end NKU_FineLastJoin
