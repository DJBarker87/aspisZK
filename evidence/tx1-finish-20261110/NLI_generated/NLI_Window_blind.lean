import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_blind (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) : Code (Out H) := do
 let row ← Array.index_usize claims 0#usize
 let blind ← Array.index_usize row 27#usize
 fold n {input:=i,next:=.alpha,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind}}
theorem blind_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) :
 run (fold (n+1) {input:=i,next:=.blind,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high}}) = run (window_blind n i l (running) (alpha) (transcript) (claims) (terminal) (low) (high)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_blind
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro row
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro blind
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms blind_head
end AspisR1.NLI_Window
end
