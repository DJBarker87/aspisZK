import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_terminalGuard (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (masked : Q) : Code (Out H) := do
 let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked
 if reject then pure (.Err r1_wire.Error.Terminal) else fold n {input:=i,next:=.mark4,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, masked:=some masked}}
theorem terminalGuard_head (n : Nat) {H : Type} (i : Input H) (l : Locals H) (running : Q) (alpha : Alpha) (transcript : r1_wire.SemanticTranscript H) (claims : Claims) (extra : Words) (masked : Q) :
 run (fold (n+1) {input:=i,next:=.terminalGuard,locals:={l with running:=some running, alpha:=some alpha, transcript:=some transcript, claims:=some claims, extra:=some extra, masked:=some masked}}) = run (window_terminalGuard n i l (running) (alpha) (transcript) (claims) (extra) (masked)) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_terminalGuard
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro reject
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases reject <;> rfl
#print axioms terminalGuard_head
end AspisR1.NLI_Window
end
