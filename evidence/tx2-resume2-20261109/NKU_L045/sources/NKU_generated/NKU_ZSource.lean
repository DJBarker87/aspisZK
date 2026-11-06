import NKU_AfterZSource
import NKK_ZStage
set_option autoImplicit false
noncomputable section
namespace NKU_ZSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (semantic : Array NKU.K 10#usize) (r : verifier.Reader) :
 Run (core.result.Result NKU.Pair verifier.Error) :=
 NKK_ZStage.source r fun x0 y0 x1 y1 claim rhs power last=>
 NKU_AfterZSource.run d s next «end» state a3 a4 g k a0 a1 rho queries semantic x0 y0 x1 y1 claim rhs power last
end NKU_ZSource
