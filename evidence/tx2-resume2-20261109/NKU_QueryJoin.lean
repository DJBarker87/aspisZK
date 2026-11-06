import NKU_QueryFirstJoin
set_option autoImplicit false
noncomputable section
namespace NKU_QueryJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) := NKU_QueryFirstJoin.run d s
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 queryBlockG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho r=
 run d (NKU_GammaPack.pack s next «end» state a3 a4 g k a0 a1 rho r) :=
 NKU_QueryFirstJoin.source d s next «end» state a3 a4 g k a0 a1 rho r
#print axioms source
end NKU_QueryJoin
