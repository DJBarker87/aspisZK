import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_highArray (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) : Code (Out H) := do
 let high ← (IDa_Deployed.boundaries i.reservation).fromFn 10#usize (FinishModel.closureFn5 i.digest) claims
 fold n {input:=i,next:=.blind,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high}}
theorem highArray_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) :
 run (fold (n+1) {input:=i,next:=.highArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low}}) = run (window_highArray n i l (running) (alpha) (transcript) (claims) (terminal) (low)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_highArray
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro high
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms highArray_head
end AspisR1.NLI_Window
end
