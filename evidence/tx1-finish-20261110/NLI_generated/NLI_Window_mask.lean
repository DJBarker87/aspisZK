import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_mask (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) : Code (Out H) := do
 let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha
 fold n {input:=i,next:=.record25a,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind, mask:=some mask}}
theorem mask_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (low : Low) (high : High) (blind : Q) :
 run (fold (n+1) {input:=i,next:=.mask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, low:=some low, high:=some high, blind:=some blind}}) = run (window_mask n i l (running) (alpha) (transcript) (claims) (terminal) (low) (high) (blind)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_mask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro mask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms mask_head
end AspisR1.NLI_Window
end
