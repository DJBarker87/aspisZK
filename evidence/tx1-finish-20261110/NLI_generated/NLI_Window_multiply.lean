import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_multiply (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (extra : Words) : Code (Out H) := do
 let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal
 fold n {input:=i,next:=.addMask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, extra:=some extra, product:=some product}}
theorem multiply_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (extra : Words) :
 run (fold (n+1) {input:=i,next:=.multiply,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, extra:=some extra}}) = run (window_multiply n i l (running) (alpha) (transcript) (claims) (terminal) (mask) (extra)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_multiply
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro product
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms multiply_head
end AspisR1.NLI_Window
end
