import NDG_IdentityLaws
set_option autoImplicit false
namespace NDG_ErrorLaws
open Aeneas Aeneas.Std Result AdapterRw

theorem length_error (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (e : solana_program_error.ProgramError) (h : a.length = .Err e)
    (clone : ops.op35 e = ok e) :
    r1_pool_adapter.owned.OwnedAccount.data_len ops a = ok (.Err e) := by
  simp [r1_pool_adapter.owned.OwnedAccount.data_len, h,
    core.result.Result.Insts.CoreCloneClone.clone,
    solana_program_error.ProgramError.Insts.CoreCloneClone, clone]

theorem length_total (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (clone : ∀ e, ops.op35 e = ok e) :
    r1_pool_adapter.owned.OwnedAccount.data_len ops a = ok a.length := by
  cases h : a.length with
  | Ok n => exact NDG_IdentityLaws.length_success ops a n h
  | Err e => exact length_error ops a e h (clone e)

theorem data_total (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (clone : ∀ e, ops.op35 e = ok e) :
    r1_pool_adapter.owned.OwnedAccount.data ops a = ok
      (match a.bytes with
       | .Ok v => .Ok (alloc.vec.Vec.deref v)
       | .Err e => .Err e) := by
  cases h : a.bytes with
  | Ok v => exact NDG_AccessLaws.data_success ops a v h
  | Err e => exact NDG_AccessLaws.data_error ops a e h (clone e)

#print axioms length_error
#print axioms length_total
#print axioms data_total
end NDG_ErrorLaws
