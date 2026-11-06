import NKU_HeaderStep
import NKU_DigestJoin
set_option autoImplicit false
noncomputable section
namespace NKU_Front
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Header/digests are installed; the remaining source suffix is explicit. -/
def suffix {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) :=
 match s.decoded.next,s.decoded.endAt with
 | some next,some «end» => do
   let reply ← NKU_DigestJoin.run d hash «end» s
   NKK_Try.emitted reply (fun (_,post)=>resumeBodyG post.frame.reservation d post.frame.checkpoint .S2 next «end»)
 | _,_ => liftM (Result.fail .panic)
theorem suffix_eq {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) : NKU_HeaderStep.suffix d hash s=suffix d hash s := by
 unfold NKU_HeaderStep.suffix suffix
 cases s.decoded.next with
 | none => rfl
 | some next =>
  cases s.decoded.endAt with
  | none => rfl
  | some «end» => exact NKU_DigestJoin.source d hash s next «end»
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_HeaderStep.run d s
 NKK_Try.emitted reply (fun (_,post)=>suffix d hash post)
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) :
 NJU_ResumeObserved.run s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash=run d hash s := by
 rw [NKU_HeaderStep.source]
 unfold run
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair => exact suffix_eq d hash pair.2
#print source
#print axioms suffix_eq
#print axioms source
end NKU_Front
