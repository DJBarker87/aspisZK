import NKU_HeaderValue
import NKU_Chronology
import NKK_HeaderFactor
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderStep
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Native header cut installed into the single parent carrier. The original
frame and owned carrier survive; decoded header values are written once. -/
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) : Stage Unit :=
 fun s => do
 let reply ← NKU_HeaderValue.value d s.frame.checkpoint .S2
 NKK_Try.emitted reply (fun (next,«end») => pure (.Ok ((),NKU.headerPost s next «end»)))
def continue {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) :=
 match s.decoded.next,s.decoded.endAt with
 | some next,some «end» => NKK_HeaderSource.afterHeader s.frame.reservation d
    s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash next «end»
 | _,_ => liftM (Result.fail .panic)
/-- This is the header-to-digest state equation at the actual parent input.
No successful-header assumption is present: every reject/abort prefix is kept.
The continuation is still the source suffix, not yet the complete native G. -/
theorem source {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (hash : H) (s : NKU.State) :
 NJU_ResumeObserved.run s.frame.reservation d s.frame.checkpoint s.frame.proof s.frame.publicBytes .S2 hash=
 (do let reply ← run d s
     NKK_Try.emitted reply (fun (_,post)=>continue d hash post)) := by
 rw [NKK_HeaderFactor.source,NKU_HeaderValue.source]
 unfold run
 rw [NKK_LogAlgebra.bind_assoc]
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply with
 | Err err => rfl
 | Ok pair => rcases pair with ⟨next,«end»⟩;rfl
#print source
#print axioms source
end NKU_HeaderStep
