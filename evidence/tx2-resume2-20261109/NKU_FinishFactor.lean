import NKU_TailSource
import NKK_ZStage
set_option autoImplicit false
noncomputable section
namespace NKU_FinishFactor
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← recordSemantic s.frame.checkpoint r.at
 NKK_Try.emitted reply fun (values,cursor)=>
 NKK_ZStage.source {r with «at» := cursor} fun x0 y0 x1 y1 claim rhs power last=>
 NKU_TailSource.native d s next «end» state a3 a4 g k a0 a1 rho queries values x0 y0 x1 y1 claim rhs power last
/-- Earlier semantic/Z factor has an opaque, separately checked tail. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 finishTailG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho queries r=
 run d s next «end» state a3 a4 g k a0 a1 rho queries r := by
 unfold finishTailG run NKK_ZStage.source NKK_FieldStages.withK NKK_FieldStages.withE NKK_Try.emitted
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases])
#print axioms source
end NKU_FinishFactor
