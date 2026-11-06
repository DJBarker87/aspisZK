import NLI_Suffix_multiply
import NLI_MonadNotation
import NLI_Window_decode25
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_decode25 {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (record25 : r1_wire.ValidatedRecord) : Code (Out H) := do
 let r ← NJM_RoundJoin.R.decode 29#usize record25 87#usize
 match r with
 | .Ok v => suffix_multiply i (running) (alpha) (transcript) (claims) (terminal) (mask) (v)
 | .Err error => pure (.Err error)
theorem decode25 {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (record25 : r1_wire.ValidatedRecord) :
 run (fold 21 {input:=i,next:=.decode25,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, record25:=some record25}}) = run (suffix_decode25 i (running) (alpha) (transcript) (claims) (terminal) (mask) (record25)) := by
 rw [NLI_Window.decode25_head 20]
 unfold NLI_Window.window_decode25 suffix_decode25
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact multiply i ({l with record25:=some record25}) (running) (alpha) (transcript) (claims) (terminal) (mask) (v)
 | Err error => rfl
#print axioms decode25
end AspisR1.NLI_Source
end
