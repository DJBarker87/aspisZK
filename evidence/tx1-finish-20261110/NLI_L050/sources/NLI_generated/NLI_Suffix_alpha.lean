import NLI_Suffix_mask
import NLI_MonadNotation
import NLI_FoldTicks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_alpha {H : Type} (i : Input H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) : Code (Out H) := do

 suffix_mask i (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)
theorem alpha {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) :
 run (fold 24 {input:=i,next:=.alpha,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind}}) = run (suffix_alpha i (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)) := by
 rw [NLI_FoldTicks.alpha 23 _ rfl]
 change run (fold 23 {input:=i,next:=.mask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind}}) = _
 exact mask i l running alpha transcript claims terminal low high blind
#print axioms alpha
end AspisR1.NLI_Source
end
