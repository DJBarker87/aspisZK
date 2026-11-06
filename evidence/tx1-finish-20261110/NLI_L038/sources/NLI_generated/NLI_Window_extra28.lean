import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_extra28 (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) : Code (Out H) := do
 let extraCell ← Array.index_usize extra 28#usize
 fold n {input:=i,next:=.addExtra,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue, extraCell:=some extraCell}}
theorem extra28_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (partialValue : Q) :
 run (fold (n+1) {input:=i,next:=.extra28,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, partialValue:=some partialValue}}) = run (window_extra28 n i l (running) (alpha) (transcript) (claims) (extra) (partialValue)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_extra28
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro extraCell
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms extra28_head
end AspisR1.NLI_Window
end
