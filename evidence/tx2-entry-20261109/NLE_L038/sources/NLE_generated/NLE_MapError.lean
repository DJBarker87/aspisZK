import NLE_OwnedTx2
set_option autoImplicit false
noncomputable section
namespace NLE_MapError
open Aeneas Aeneas.Std Result AdapterRw
abbrev VE := aspis_r1_cost_probe.verifier.Error
abbrev PE := solana_program_error.ProgramError
/-- The exact emitted map_err continuation may itself fail/div; all arms
remain represented rather than collapsed to a single ProgramError tag. -/
def run (ops : Ops) (reply : core.result.Result Unit VE) :
 Result (core.result.Result Unit PE) :=
 core.result.Result.map_err (BuiltinFnOnce VE PE) reply ops.op44
theorem success (ops : Ops) : run ops (.Ok ()) = ok (.Ok ()) := rfl
theorem rejection (ops : Ops) (err : VE) : run ops (.Err err) = (do
 let converted ← ops.op44 err
 ok (.Err converted)) := rfl
theorem abort (ops : Ops) (err : VE) (failure : Error)
 (failed : ops.op44 err = .fail failure) : run ops (.Err err) = .fail failure := by
 rw [rejection,failed]
 rfl
theorem diverge (ops : Ops) (err : VE)
 (failed : ops.op44 err = .div) : run ops (.Err err) = .div := by
 rw [rejection,failed]
 rfl
#print rejection
#print abort
#print diverge
#print axioms success
#print axioms rejection
#print axioms abort
#print axioms diverge
end NLE_MapError
