import NKU_State
set_option autoImplicit false
noncomputable section
namespace NKU_GammaPack
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
def pack (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (r : verifier.Reader) : NKU.State :=
 {s with phase := .queries,reader := r,decoded := {s.decoded with next := some next,endAt := some «end»,roots := [state,a3,a4],gammaAlpha := [g,k,a0,a1],rho := some rho}}
theorem frame (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 (pack s next «end» state a3 a4 g k a0 a1 rho r).frame=s.frame := rfl
#print axioms frame
end NKU_GammaPack
