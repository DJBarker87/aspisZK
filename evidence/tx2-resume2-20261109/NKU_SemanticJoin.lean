import NKU_FinishTransport
import NKU_ZJoin
set_option autoImplicit false
noncomputable section
namespace NKU_SemanticJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_Semantic.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_ZJoin.run d post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (r : verifier.Reader) :
 finishTailG s.frame.reservation d s.frame.checkpoint .S2 next «end» state a3 a4 g k a0 a1 rho queries r=
 run d (NKU_Pack.pack s next «end» state a3 a4 g k a0 a1 rho queries r) := by
 rw [NKU_FinishTransport.source]
 unfold NKU_SemanticSource.run run NKU_Semantic.run
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair =>
  rcases pair with ⟨values,cursor⟩
  simpa only [NKU_Pack.pack,NKU_Semantic.post,NKK_LogReduce.pure_bind] using
   NKU_ZJoin.source d s next «end» state a3 a4 g k a0 a1 rho queries values {r with «at» := cursor}
#print axioms source
end NKU_SemanticJoin
