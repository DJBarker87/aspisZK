import NLI_Suffix_alpha
import NLI_MonadNotation
import NLI_Window_blind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_blind {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) : Code (Out H) := do
 let row ← Array.index_usize claims 0#usize
 let blind ← Array.index_usize row 27#usize
 suffix_alpha i (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)
theorem blind {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) :
 run (fold 25 {input:=i,next:=.blind,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high}}) = run (suffix_blind i (running) (alpha) (transcript) (claims) (terminal) (low) (high)) := by
 rw [NLI_Window.blind_head 24]
 unfold NLI_Window.window_blind suffix_blind
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro row
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro blind
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 exact NLI_Source.alpha i (l) (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)
#print axioms blind
end AspisR1.NLI_Source
end
