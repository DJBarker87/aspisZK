import NLC_FinishStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Independent actual terminal error, not selected from original proof bytes. -/
theorem map_error {H : Type} (i : Input H) (l : Locals H)
 (e : aspis_core.state_only_prefix.r0.Error) :
 run (step {input:=i,locals:={l with terminalReply:=some (.Err e)},next:=.mapPublic}) =
 ([],ok (.inl (.Err r1_wire.Error.Public))) := by rfl
/-- The exact returned value is stored in the SAME state; all other slots and
input fields stay in that state. This is a source-step law, not a native root. -/
theorem map_value {H : Type} (i : Input H) (l : Locals H) (q : Q) :
 let before : State H := {input:=i,locals:={l with terminalReply:=some (.Ok q)},next:=.mapPublic}
 run (step before) = ([],ok (.inr (put before .mark3 {before.locals with terminal:=some q}))) := by rfl
#print axioms map_error
#print axioms map_value
#print map_error
#print map_value
end AspisR1.NLC_Finish
end
