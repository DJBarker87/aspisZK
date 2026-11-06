import NKU_Fold
import NKU_FineZJoin
set_option autoImplicit false
noncomputable section
namespace NKU_FineSemanticJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem installed {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) :
 NKU_Fold.semantic d s=NKU_SemanticJoin.run d s := by
 simp only [NKU_Fold.semantic,NKU_SemanticJoin.run,NKU_FineZJoin.installed]
#print axioms installed
end NKU_FineSemanticJoin
