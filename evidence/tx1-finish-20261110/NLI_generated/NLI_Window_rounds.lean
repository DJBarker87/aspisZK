import NLI_MonadNotation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Window
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
def window_rounds (n : Nat) {H : Type} (i : Input H) (l : Locals H)  : Code (Out H) := do
 let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript
 match r with
 | .Ok v => fold n {input:=i,next:=.mark2,locals:={l with running:=some v.1, alpha:=some v.2.1, transcript:=some v.2.2}}
 | .Err error => pure (.Err error)
theorem rounds_head (n : Nat) {H : Type} (i : Input H) (l : Locals H)  :
 run (fold (n+1) {input:=i,next:=.rounds,locals:=l}) = run (window_rounds n i l ) := by
 rw [fold]
 simp only [step,NLC_Finish.read]
 unfold window_rounds
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r <;> rfl
#print axioms rounds_head
end AspisR1.NLI_Window
end
