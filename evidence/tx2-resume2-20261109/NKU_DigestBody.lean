import NKU_BodyJoin
import NKU_DigestJoin
set_option autoImplicit false
noncomputable section
namespace NKU_DigestBody
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) (next : U8) («end» : Usize) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_DigestJoin.run d hash «end» s
 NKK_Try.emitted reply (fun (_,post)=>NKU_BodyJoin.run d (NKU_HeaderSlots.set post next «end»))
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) (next : U8) («end» : Usize) :
 NKK_HeaderSource.afterHeader s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash next «end»=
 run d hash s next «end» := by
 rw [NKU_DigestJoin.source]
 unfold run
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair => exact NKU_BodyJoin.source d pair.2 next «end»
#print axioms source
end NKU_DigestBody
