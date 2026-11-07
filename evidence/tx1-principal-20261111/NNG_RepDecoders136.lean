import NNG_Representation136
import NNG_LIBRounds
import NNG_LIBTerminal
import NNG_LIBCircle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_RepDecoders136
open Aeneas Aeneas.Std Result NNG_Representation136

theorem rounds (a : Args) : NNG_DProjection136.rounds (project a) = NNG_LIBRounds.projectReply a.challenges.eta := by
  funext r
  cases r with
  | Err e => rfl
  | Ok val => rcases val with ⟨q,alpha,t⟩;rfl
#print axioms rounds

theorem terminal (a : Args) : NNG_DProjection136.terminalReply (project a) = NNG_LIBTerminal.projectReply a.challenges.eta := by
  funext r
  cases r <;> rfl
#print axioms terminal

theorem circle (a : Args) : NNG_DProjection136.circleReply (project a) = NNG_LIBCircle.project := by
  funext pair
  rcases pair with ⟨r,t⟩
  cases r <;> rfl
#print axioms circle
end AspisR1.NNG_RepDecoders136
