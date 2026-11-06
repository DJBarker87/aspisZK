import NKU_ZSource
import NKU_AfterZ
set_option autoImplicit false
noncomputable section
namespace NKU_ZJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_ZClaim.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_AfterZ.run d post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (semantic : Array NKU.K 10#usize) (r : verifier.Reader) :
 NKU_ZSource.run d s next «end» state a3 a4 g k a0 a1 rho queries semantic r=
 run d (NKU_Semantic.post (NKU_Pack.pack s next «end» state a3 a4 g k a0 a1 rho queries r) semantic r.at) := by
 unfold run
 rw [←NKU_ZClaim.source_eq_run]
 unfold NKU_ZSource.run NKU_ZClaim.source NKK_ZStage.source NKK_FieldStages.withK NKK_FieldStages.withE NKU_ZClaim.reply
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKU_AfterZ.source)
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_Semantic.post,NKU_Pack.pack])
#print axioms source
end NKU_ZJoin
