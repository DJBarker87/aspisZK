import NNH_MappedOk
set_option autoImplicit false
namespace NNH_ClockOk
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

theorem value (clock : core.result.Result U64 solana_program_error.ProgramError) (time : UInt64)
 (success : reply slot clock=.ok time) :
 ∃ t,clock=.Ok t ∧ slot t=time := by
 cases clock with
 | Err e => cases success
 | Ok t => exact ⟨t,rfl,Except.ok.inj success⟩
#print axioms value
end NNH_ClockOk
