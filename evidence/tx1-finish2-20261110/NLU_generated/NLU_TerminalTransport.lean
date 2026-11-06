import NLU_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
/-- The delivered256 fold, converted through exactly FIq_Terminal's full
outer/inner Result boundary. No independently selected successful reply. -/
def nativeTerminal (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
 (c : r1_wire.Challenges) : Result (core.result.Result aspis_core.field.QM31 FIq_Terminal.Error) := do
 let result ← NLH_WrapperRoot.reference (toPublic pub) (mapArray (mapArray toQ) claims)
   (mapArray toQ alpha) (toChallenges c)
 match result with
 | .Ok q => ok (.Ok (fromQ q))
 | .Err e => ok (.Err (FIq_Terminal.fromError e))
theorem installed (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
 (c : r1_wire.Challenges) (domain : InputDomain pub c)
 (hc : ∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row)
 (ha : FIw_ArrayValue.canonical (mapArray toQ alpha)) :
 nativeTerminal pub claims alpha c=FIq_Terminal.terminal pub claims alpha c := by
 obtain ⟨result,events,cuts,attemptedPrefix,canonical,projected,reference⟩:=install pub claims alpha c domain hc ha
 unfold nativeTerminal FIq_Terminal.terminal
 rw [reference]
 rfl
#print axioms installed
set_option pp.proofs false in #print installed
end AspisR1.NLU_Terminal
end
