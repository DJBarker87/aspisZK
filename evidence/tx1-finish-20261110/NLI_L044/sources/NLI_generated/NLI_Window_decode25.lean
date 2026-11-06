import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_decode25 (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (record25 : r1_wire.ValidatedRecord) : Code (Out H) := do
 let r ← NJM_RoundJoin.R.decode 29#usize record25 87#usize
 match r with
 | .Ok v => fold n {input:=i,next:=.multiply,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, record25:=some record25, extra:=some v}}
 | .Err error => pure (.Err error)
theorem decode25_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (terminal : Q) (mask : Q) (record25 : r1_wire.ValidatedRecord) :
 run (fold (n+1) {input:=i,next:=.decode25,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, terminal:=some terminal, mask:=some mask, record25:=some record25}}) = run (window_decode25 n i l (running) (alpha) (transcript) (claims) (terminal) (mask) (record25)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_decode25
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r <;> rfl
#print axioms decode25_head
end AspisR1.NLI_Window
end
