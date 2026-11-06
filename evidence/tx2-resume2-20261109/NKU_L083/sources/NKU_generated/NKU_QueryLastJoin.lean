import NKU_QueryEnd
import NKU_SemanticJoin
import NKU_QueryPack
import NKK_QueryEndJoin
set_option autoImplicit false
noncomputable section
namespace NKU_QueryLastJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_QueryEnd.run s
 NKK_Try.emitted reply fun (_,post)=>do
 let valid ← NKU_Validator.run post
 NKK_Try.emitted valid fun (_,checked)=>NKU_SemanticJoin.run d checked
/-- Last six native reads, followed by validator35 at the SAME22-word array. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 : U32) (r : verifier.Reader) :
 queryEndG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r=
 run d (NKU_QueryPack.pack s next «end» state a3 a4 g k a0 a1 rho [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15] r) := by
 rw [NKK_QueryEndJoin.source]
 unfold run NKU_QueryEnd.run NKU_Validator.run
 simp only [NKK_QueryStage.stage6]
 unfold NKK_QueryStage.source6 NKK_QueryEndJoin.next
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_QueryPack.pack,NKU_GammaPack.pack,NKU_QueryEnd.post,NKU_Validator.values,List.cons_append,List.nil_append]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b0,r0⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b1,r1⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b2,r2⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b3,r3⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b4,r4⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b5,r5⟩
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok unit =>
  cases unit
  apply NKU_SemanticJoin.source
#print axioms source
end NKU_QueryLastJoin
