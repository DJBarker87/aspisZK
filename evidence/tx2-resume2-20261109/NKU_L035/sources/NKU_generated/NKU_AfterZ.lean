import NKU_AfterZSource
import NKU_Allocation
import NKU_Weights
import NKU_Tail
set_option autoImplicit false
noncomputable section
namespace NKU_AfterZ
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_Allocation.run d s
 NKK_Try.emitted reply fun (_,allocated)=>do
 let weights ← NKU_Weights.run allocated
 NKK_Try.emitted weights fun (_,weighted)=>NKU_Tail.run weighted
/-- Full source continuation at43 joins the SAME allocation44 and weights45
and terminal value. Every error/abort pack is preserved. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize)
 (state a3 a4 : Array U8 32#usize) (g k a0 a1 : NKU.E) (rho : NKU.K)
 (queries : Array U32 22#usize) (semantic : Array NKU.K 10#usize)
 (x0 y0 x1 y1 : NKU.K) (claim rhs : NKU.E) (power : NKU.K) (r : verifier.Reader) :
 NKU_AfterZSource.run d s next «end» state a3 a4 g k a0 a1 rho queries semantic x0 y0 x1 y1 claim rhs power r=
 run d (NKU_ZClaim.post (NKU_Semantic.post
   (NKU_Pack.pack s next «end» state a3 a4 g k a0 a1 rho queries r) semantic r.at)
   x0 y0 x1 y1 claim rhs power r) := by
 unfold NKU_AfterZSource.run run NKU_Allocation.run NKU_Weights.run
 simp only [NKK_LogAlgebra.bind_assoc,NKK_Try.branch,NKK_LogReduce.pure_bind]
 apply NKK_LogAlgebra.bind_congr
 intro allocated
 cases allocated with
 | Err err => rfl
 | Ok owner =>
  apply NKK_LogAlgebra.bind_congr
  intro reply
  cases reply with
  | Err err => rfl
  | Ok pair =>
   rcases pair with ⟨weights,cursor⟩
   unfold NKU_Tail.run NKU_Tail.build NKU_Weights.post NKU_Allocation.post NKU_ZClaim.post NKU_Semantic.post NKU_Pack.pack
   simp only [NKU_Array22.source]
   split <;> rfl
#print source
#print axioms source
end NKU_AfterZ
