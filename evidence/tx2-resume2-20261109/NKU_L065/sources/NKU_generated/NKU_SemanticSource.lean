import NKU_ZSource
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKU_SemanticSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← recordSemantic s.frame.checkpoint r.at
 NKK_Try.emitted reply fun (values,cursor)=>
 NKU_ZSource.run d s next «end» state a3 a4 g k a0 a1 rho queries values {r with «at» := cursor}
end NKU_SemanticSource
