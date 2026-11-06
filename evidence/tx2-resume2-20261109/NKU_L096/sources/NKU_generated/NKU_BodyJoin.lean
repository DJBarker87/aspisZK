import NKU_GammaJoin
import NKU_Roots
import NKU_HeaderSlots
import NKK_ResumeBodyFactor
set_option autoImplicit false
noncomputable section
namespace NKU_BodyJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_Roots.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_GammaJoin.run d post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (next : U8) («end» : Usize) :
 resumeBodyG s.frame.reservation d s.frame.checkpoint .S2 next «end»=
 run d (NKU_HeaderSlots.set s next «end») := by
 rw [NKK_ResumeBodyFactor.source]
 unfold run NKU_Roots.run
 rw [NKK_RawPrefix.source]
 unfold NKK_RawPrefix.literal NKK_ResumeBodyFactor.afterRoots
 repeat' first
 | rfl
 | (apply NKU_GammaJoin.source)
 | (cases_type Prod)
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKU_Roots.entry,NKU_Roots.post,NKU_HeaderSlots.set])
 | (apply NKK_LogAlgebra.bind_congr;intro value)
#print axioms source
end NKU_BodyJoin
