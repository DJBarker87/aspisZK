import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_lowArray (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) : Code (Out H) := do
 let low ← (IDa_Deployed.boundaries i.reservation).fromFn 16#usize (FinishModel.closureFn9 i.digest) claims
 fold n {input:=i,next:=.highArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low}}
theorem lowArray_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) :
 run (fold (n+1) {input:=i,next:=.lowArray,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal}}) = run (window_lowArray n i l (running) (alpha) (transcript) (claims) (terminal)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_lowArray
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro low
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms lowArray_head
end AspisR1.NLI_Window
end
