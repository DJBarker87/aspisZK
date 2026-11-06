import NLI_Suffix_mark3
import NLI_MonadNotation
import NLI_Window_mapPublic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_mapPublic {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminalReply : core.result.Result Q aspis_core.state_only_prefix.r0.Error) : Code (Out H) := do
 let r ← core.result.Result.map_err (FinishModel.closureFn11 i.digest) terminalReply ()
 match r with
 | .Ok v => suffix_mark3 i (running) (alpha) (transcript) (claims) (v)
 | .Err error => pure (.Err error)
theorem mapPublic {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminalReply : core.result.Result Q aspis_core.state_only_prefix.r0.Error) :
 run (fold 29 {input:=i,next:=.mapPublic,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminalReply:=some terminalReply}}) = run (suffix_mapPublic i (running) (alpha) (transcript) (claims) (terminalReply)) := by
 rw [NLI_Window.mapPublic_head 28]
 unfold NLI_Window.window_mapPublic suffix_mapPublic
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact NLI_Source.mark3 i ({l with terminalReply:=some terminalReply}) (running) (alpha) (transcript) (claims) (v)
 | Err error => rfl
#print axioms mapPublic
end AspisR1.NLI_Source
end
