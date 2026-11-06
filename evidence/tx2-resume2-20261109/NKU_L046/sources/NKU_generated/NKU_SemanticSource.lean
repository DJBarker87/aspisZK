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
/-- Factor the actual suffix into semantic36, mixed37–43 and owned44–45.
The model has no loop followed by an explicit return in this frozen body;
weights' for-loop has only its tail Ok after it (bc inspection recorded). -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 finishTailG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho queries r=
 run d s next «end» state a3 a4 g k a0 a1 rho queries r := by
 unfold finishTailG run NKU_ZSource.run NKK_ZStage.source NKK_FieldStages.withK NKK_FieldStages.withE NKU_AfterZSource.run NKK_AllocationStage.source
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases])
#print axioms source
end NKU_SemanticSource
