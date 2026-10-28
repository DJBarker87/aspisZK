import S2W_D189Wrappers
set_option autoImplicit false
namespace AspisR1.NCL_OwnedModels
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem key (account : r1_pool_adapter.owned.OwnedAccount) :
    r1_pool_adapter.owned.OwnedAccount.impl.key account=ok account.key := rfl

theorem owner (account : r1_pool_adapter.owned.OwnedAccount) :
    r1_pool_adapter.owned.OwnedAccount.impl.owner account=ok account.owner := rfl

/-- Exact emitted predicate, paired with the full-Boolean native gate. -/
theorem readonly (signer writable executable : Bool) :
    r1_pool_adapter.readonly_buffer_meta_ok signer writable executable=
      ok (if signer || writable || executable then
        core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData
        else core.result.Result.Ok ()) := by
  cases signer <;> cases writable <;> cases executable <;> rfl

theorem owned_readonly (account : r1_pool_adapter.owned.OwnedAccount) :
    r1_pool_adapter.owned.require_readonly_buffer account=
      ok (if account.is_signer || account.is_writable || account.executable then
        core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData
        else core.result.Result.Ok ()) :=
  readonly account.is_signer account.is_writable account.executable

theorem data_ok (ops : Ops) (account : r1_pool_adapter.owned.OwnedAccount)
    (bytes : alloc.vec.Vec U8) (stored : account.bytes=core.result.Result.Ok bytes) :
    r1_pool_adapter.owned.OwnedAccount.data ops account=ok (.Ok bytes.deref) := by
  rw [r1_pool_adapter.owned.OwnedAccount.data,stored]

/-- Clone's full Result/fail/div remains in the model statement. No successful
or identity clone is supplied for an arbitrary ProgramError. -/
theorem data_error (ops : Ops) (account : r1_pool_adapter.owned.OwnedAccount)
    (error : solana_program_error.ProgramError) (stored : account.bytes=core.result.Result.Err error) :
    r1_pool_adapter.owned.OwnedAccount.data ops account=
      (do let cloned ← ops.op35 error;ok (core.result.Result.Err (T := Slice U8) cloned)) := by
  rw [r1_pool_adapter.owned.OwnedAccount.data,stored]

theorem length_ok (ops : Ops) (account : r1_pool_adapter.owned.OwnedAccount)
    (size : Usize) (stored : account.length=core.result.Result.Ok size) :
    r1_pool_adapter.owned.OwnedAccount.data_len ops account=ok (.Ok size) := by
  rw [r1_pool_adapter.owned.OwnedAccount.data_len,stored]
  rfl

#print axioms key
#print axioms owner
#print axioms readonly
#print axioms owned_readonly
#print axioms data_ok
#print axioms data_error
#print axioms length_ok
end AspisR1.NCL_OwnedModels
