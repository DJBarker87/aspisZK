import NKU_QueryFirst
import NKU_QueryMiddleJoin
import NKK_QueryBlockJoin
set_option autoImplicit false
noncomputable section
namespace NKU_QueryFirstJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_QueryFirst.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_QueryMiddleJoin.run d post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K) (r : verifier.Reader) :
 queryBlockG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho  r=
 run d (NKU_GammaPack.pack s next «end» state a3 a4 g k a0 a1 rho r) := by
 rw [NKK_QueryBlockJoin.source]
 unfold run NKU_QueryFirst.run
 simp only [NKK_QueryStage.stage8]
 unfold NKK_QueryStage.source8 NKK_QueryBlockJoin.next
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_QueryPack.pack,NKU_GammaPack.pack,NKU_QueryFirst.post,List.cons_append,List.nil_append]
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
 rintro ⟨b6,r6⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b7,r7⟩
 simpa only [NKU_QueryPack.pack,NKU_GammaPack.pack,NKU_QueryFirst.post,List.cons_append,List.nil_append] using
  NKU_QueryMiddleJoin.source d s next «end» state a3 a4 g k a0 a1 rho  (core.num.U32.from_le_bytes b0) (core.num.U32.from_le_bytes b1) (core.num.U32.from_le_bytes b2) (core.num.U32.from_le_bytes b3) (core.num.U32.from_le_bytes b4) (core.num.U32.from_le_bytes b5) (core.num.U32.from_le_bytes b6) (core.num.U32.from_le_bytes b7) r7
#print axioms source
end NKU_QueryFirstJoin
