import NDH_RegistrySlots
set_option autoImplicit false
namespace NDH_RegistryTail
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry

def reject : Result (core.result.Result Unit solana_program_error.ProgramError) :=
  ok (.Err .InvalidAccountData)

/-- Exact local boolean/control tail of the coherent owned V1 caller. -/
def tailV1 (ops : Ops) (r : VerifierRegistryV1)
    (next : Result (core.result.Result Unit solana_program_error.ProgramError)) := do
  let immutable ← ops.op26 r
  if immutable then
    let paused ← ops.op25 r
    if paused then reject else next
  else reject

/-- Exact corresponding tail in the V2 branch. -/
def tailV2 (ops : Ops) (r : VerifierRegistryV2)
    (next : Result (core.result.Result Unit solana_program_error.ProgramError)) := do
  let immutable ← ops.op28 r
  if immutable then
    let paused ← ops.op27 r
    if paused then reject else next
  else reject

theorem v1 (base : Ops) (r : VerifierRegistryV1)
    (next : Result (core.result.Result Unit solana_program_error.ProgramError)) :
    tailV1 (NDH_RegistrySlots.install base) r next = (do
      let immutable ← NDH_Reference.flag_ref r.flags 2#u8
      if immutable then
        let paused ← NDH_Reference.flag_ref r.flags 1#u8
        if paused then reject else next
      else reject) := rfl

theorem v2 (base : Ops) (r : VerifierRegistryV2)
    (next : Result (core.result.Result Unit solana_program_error.ProgramError)) :
    tailV2 (NDH_RegistrySlots.install base) r next = (do
      let immutable ← NDH_Reference.flag_ref r.flags 2#u8
      if immutable then
        let paused ← NDH_Reference.flag_ref r.flags 1#u8
        if paused then reject else next
      else reject) := rfl

#print axioms v1
#print axioms v2
end NDH_RegistryTail
