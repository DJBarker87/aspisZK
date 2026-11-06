import NKU_GammaPack
set_option autoImplicit false
noncomputable section
namespace NKU_QueryPack
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
def pack (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (qs : List U32) (r : verifier.Reader) : NKU.State :=
 let out:=NKU_GammaPack.pack s next «end» state a3 a4 g k a0 a1 rho r
 {out with decoded := {out.decoded with queries := qs}}
end NKU_QueryPack
