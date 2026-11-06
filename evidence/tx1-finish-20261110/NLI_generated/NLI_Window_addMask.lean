import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_addMask (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (mask : Q) (extra : Words) (product : Q) : Code (Out H) := do
 let partialValue ← (IDa_Deployed.boundaries i.reservation).add mask product
 fold n {input:=i,next:=.extra28,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, mask:=some mask, extra:=some extra, product:=some product, partialValue:=some partialValue}}
theorem addMask_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (mask : Q) (extra : Words) (product : Q) :
 run (fold (n+1) {input:=i,next:=.addMask,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, mask:=some mask, extra:=some extra, product:=some product}}) = run (window_addMask n i l (running) (alpha) (transcript) (claims) (mask) (extra) (product)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_addMask
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro partialValue
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 rfl
#print axioms addMask_head
end AspisR1.NLI_Window
end
