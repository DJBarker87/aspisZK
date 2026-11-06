import NKU_Gamma
import NKU_Semantic
import NKU_ZClaim
set_option autoImplicit false
noncomputable section
namespace NKU_Pack
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
def prefix (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) : NKU.State :=
 {s with phase := .semantic,reader := r,decoded := {s.decoded with next := some next,endAt := some «end»,roots := [state,a3,a4],gammaAlpha := [g,k,a0,a1],rho := some rho,queries := queries.val}}
theorem frame (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 (prefix s next «end» state a3 a4 g k a0 a1 rho queries r).frame=s.frame := rfl
#print axioms frame
end NKU_Pack
