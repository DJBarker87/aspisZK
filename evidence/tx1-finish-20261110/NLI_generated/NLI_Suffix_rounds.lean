import NLI_Suffix_mark2
import NLI_MonadNotation
import NLI_Window_rounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- Readless source continuation; no native credit is asserted. -/
def suffix_rounds {H : Type} (i : Input H)  : Code (Out H) := do
 let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript
 match r with
 | .Ok v => suffix_mark2 i (v.1) (v.2.1) (v.2.2)
 | .Err error => pure (.Err error)
theorem rounds {H : Type} (i : Input H) (l : Locals H)  :
 run (fold 34 {input:=i,next:=.rounds,locals:=l}) = run (suffix_rounds i ) := by
 rw [NLI_Window.rounds_head 33]
 unfold NLI_Window.window_rounds suffix_rounds
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 apply NLI_Notation.congr_bind
 intro r
 try simp only [NLI_Notation.assoc,NLI_Notation.pure_left,NLI_Notation.lift_ok]
 cases r with
 | Ok v => exact mark2 i (l) (v.1) (v.2.1) (v.2.2)
 | Err error => rfl
#print axioms rounds
end AspisR1.NLI_Source
end
