import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_record25a (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) : Code (Out H) := do
 let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
 match r with
 | .Ok v => fold n {input:=i,next:=.decode25,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, record25:=some v}}
 | .Err error => pure (.Err error)
theorem record25a_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) :
 run (fold (n+1) {input:=i,next:=.record25a,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask}}) = run (window_record25a n i l (running) (alpha) (transcript) (claims) (terminal) (mask)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_record25a
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r <;> rfl
#print axioms record25a_head
end AspisR1.NLI_Window
end
