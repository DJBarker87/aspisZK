import NLI_RowSpec256
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_TerminalStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish NLI_TerminalInterface
open PreparedHashCode (Code run)
theorem reply_exact (native : Native) (packet : RowSpec_256 native)
 (A : Type) (heap : A) (publicValue : Public) (claims : Claims)
 (alpha : Alpha) (challenges : Challenges) :
 (native A heap publicValue claims alpha challenges).reply=
 FIq_Terminal.terminal publicValue claims alpha challenges :=
 (packet A heap publicValue claims alpha challenges).2.2.2.2.2.2

def nativeStep {A H : Type} (native : Native) (heap : A) (s : State H) : Code (Post H) := do
 let c ← read s.locals.claims
 let a ← read s.locals.alpha
 let r ← (native A heap s.input.publicValue c a s.input.challenges).reply
 pure (.inr (put s .mapPublic {s.locals with terminalReply:=some r}))
/-- Conditional child step only, at SAME arguments; no136 root is emitted.
The RowSpec256 packet is OPEN, and may be discharged only by its actual
native producer after review. Missing-slot fail and child fail/div are kept. -/
theorem to_source {A H : Type} (native : Native) (packet : RowSpec_256 native)
 (heap : A) (s : State H) (atSite : s.next=.terminal) :
 run (nativeStep native heap s)=run (step s) := by
 rw [step_terminal s atSite]
 unfold nativeStep window_terminal
 simp_rw [reply_exact native packet]
 rfl
#print axioms reply_exact
#print axioms to_source
#print to_source
end AspisR1.NLI_TerminalStep
end
