import NKU_QueryFirst
import NKU_QueryMid
import NKU_QueryEnd
import NKU_SemanticJoin
import NKU_GammaPack
import NKK_QueryBlockJoin
import NKK_QueryMidJoin
import NKK_QueryEndJoin
set_option autoImplicit false
noncomputable section
namespace NKU_QueryJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let a ← NKU_QueryFirst.run s
 NKK_Try.emitted a fun (_,s1)=>do
 let b ← NKU_QueryMid.run s1
 NKK_Try.emitted b fun (_,s2)=>do
 let c ← NKU_QueryEnd.run s2
 NKK_Try.emitted c fun (_,s3)=>do
 let v ← NKU_Validator.run s3
 NKK_Try.emitted v fun (_,s4)=>NKU_SemanticJoin.run d s4
/-- Source windows13–34 and validator35 install on the SAME preceding state.
The existing 8/8/6 native cuts and joins are used with their actual replies. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 queryBlockG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho r=
 run d (NKU_GammaPack.pack s next «end» state a3 a4 g k a0 a1 rho r) := by
 unfold queryBlockG queryMidG queryEndG run NKU_QueryFirst.run NKU_QueryMid.run NKU_QueryEnd.run NKU_Validator.run
 simp only [NKK_QueryStage.stage8,NKK_QueryStage.stage6]
 unfold NKK_QueryStage.source8 NKK_QueryStage.source6
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKU_SemanticJoin.source)
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_QueryFirst.post,NKU_QueryMid.post,NKU_QueryEnd.post,NKU_GammaPack.pack,NKU_Validator.values,List.append_cons,List.nil_append])
#print axioms source
end NKU_QueryJoin
