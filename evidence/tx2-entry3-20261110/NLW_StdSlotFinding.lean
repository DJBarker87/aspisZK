import NLW_GetterSuccess
set_option autoImplicit false
noncomputable section
namespace NLW_StdSlotFinding
open Aeneas Aeneas.Std Result AdapterRw
/-- A source Ops name is not a standard-library implementation law. This
counterexample is about an arbitrary SOURCE dictionary, not the frozen Rust
or a reached deployed execution. No release counterexample is asserted. -/
def badClone (ops : Ops) : Ops := {ops with op35:=fun _=>.fail .panic}
theorem source_error_can_abort (ops : Ops)
 (a : r1_pool_adapter.owned.OwnedAccount)
 (stored : a.bytes=.Err solana_program_error.ProgramError.InvalidAccountData) :
 r1_pool_adapter.owned.OwnedAccount.data (badClone ops) a=.fail .panic := by
 simp [r1_pool_adapter.owned.OwnedAccount.data,badClone,stored]
/-- The successful getter projection needs no such slot law. Error-path
installation remains a separate typed std/native obligation. -/
theorem badClone_does_not_affect_success (ops : Ops)
 (a : r1_pool_adapter.owned.OwnedAccount) (bytes : Slice U8)
 (stored : a.bytes=.Ok bytes) :
 r1_pool_adapter.owned.OwnedAccount.data (badClone ops) a=.ok (.Ok bytes) :=
 NLW_GetterSuccess.returned (badClone ops) a bytes stored
#print source_error_can_abort
#print badClone_does_not_affect_success
#print axioms source_error_can_abort
#print axioms badClone_does_not_affect_success
end NLW_StdSlotFinding
