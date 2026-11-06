import NKU_QueryJoin
import NKU_RootPack
import NKU_Gamma
set_option autoImplicit false
noncomputable section
namespace NKU_GammaJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_Gamma.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_QueryJoin.run d post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (r : verifier.Reader) :
 (NKK_FieldStages.gamma r fun g k a0 a1 rho last=>
  queryBlockG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho last)=
 run d (NKU_RootPack.pack s next «end» state a3 a4 r) := by
 unfold run
 rw [←NKU_Gamma.source_eq_run]
 unfold NKU_Gamma.source NKK_FieldStages.gamma NKK_FieldStages.withK NKK_FieldStages.withE NKU_Gamma.reply
 repeat' first
 | rfl
 | (apply NKU_QueryJoin.source)
 | (cases_type core.result.Result)
 | (cases_type Prod)
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_RootPack.pack,NKU_Gamma.post])
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
#print axioms source
end NKU_GammaJoin
