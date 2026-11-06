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
 simp only [NKK_RawPrefix.literal,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases,NKK_ResumeBodyFactor.afterRoots,NKU_Roots.entry,NKU_Roots.post,NKU_HeaderSlots.set]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b0,r0⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b1,r1⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b2,r2⟩
 simpa only [NKU_RootPack.pack] using NKU_GammaJoin.source d s next «end» b0 b1 b2 r2

#print axioms source
end NKU_BodyJoin
