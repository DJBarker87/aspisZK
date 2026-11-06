import NLI_Suffix_original
import NLI_MonadNotation
import NLI_Window_claims
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_claims {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) : Code (Out H) := do
 let r ← (IDa_Deployed.boundaries i.reservation).claims i.prefix1
 match r with
 | .Ok v => suffix_original i (running) (alpha) (transcript) (v)
 | .Err error => pure (.Err error)
theorem claims {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) :
 run (fold 32 {input:=i,next:=.claims,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript}}) = run (suffix_claims i (running) (alpha) (transcript)) := by
 rw [NLI_Window.claims_head 31]
 unfold NLI_Window.window_claims suffix_claims
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact original i (l) (running) (alpha) (transcript) (v)
 | Err error => rfl
#print axioms claims
end AspisR1.NLI_Source
end
