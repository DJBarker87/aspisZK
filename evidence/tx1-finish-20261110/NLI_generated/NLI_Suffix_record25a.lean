import NLI_Suffix_decode25
import NLI_MonadNotation
import NLI_Window_record25a
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_record25a {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) : Code (Out H) := do
 let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
 match r with
 | .Ok v => suffix_decode25 i (running) (alpha) (transcript) (claims) (terminal) (mask) (v)
 | .Err error => pure (.Err error)
theorem record25a {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) :
 run (fold 22 {input:=i,next:=.record25a,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask}}) = run (suffix_record25a i (running) (alpha) (transcript) (claims) (terminal) (mask)) := by
 rw [NLI_Window.record25a_head 21]
 unfold NLI_Window.window_record25a suffix_record25a
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact decode25 i (l) (running) (alpha) (transcript) (claims) (terminal) (mask) (v)
 | Err error => rfl
#print axioms record25a
end AspisR1.NLI_Source
end
