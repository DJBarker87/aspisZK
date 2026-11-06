import NLI_Suffix_addExtra
import NLI_MonadNotation
import NLI_Window_extra28
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_extra28 {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) : Code (Out H) := do
 let extraCell ← Array.index_usize extra 28#usize
 suffix_addExtra i (running) (alpha) (transcript) (claims) (extra) (partialValue) (extraCell)
theorem extra28 {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) :
 run (fold 18 {input:=i,next:=.extra28,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue}}) = run (suffix_extra28 i (running) (alpha) (transcript) (claims) (extra) (partialValue)) := by
 rw [NLI_Window.extra28_head 17]
 unfold NLI_Window.window_extra28 suffix_extra28
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro extraCell
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact addExtra i (l) (running) (alpha) (transcript) (claims) (extra) (partialValue) (extraCell)
#print axioms extra28
end AspisR1.NLI_Source
end
