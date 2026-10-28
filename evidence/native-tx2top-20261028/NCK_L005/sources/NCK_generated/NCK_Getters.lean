import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NCK_Getters
open Aeneas Aeneas.Std Result
open AdapterRw.r1_pool_adapter.owned

theorem key_exact (a : OwnedAccount) : OwnedAccount.impl.key a = ok a.key := rfl
 theorem owner_exact (a : OwnedAccount) : OwnedAccount.impl.owner a = ok a.owner := rfl
 theorem data_ok (ops : AdapterRw.Ops) (a : OwnedAccount) (v : alloc.vec.Vec U8)
    (bytes : a.bytes = .Ok v) : OwnedAccount.data ops a = ok (.Ok v.deref) := by
  simp only [OwnedAccount.data, bytes]
 theorem data_error (ops : AdapterRw.Ops) (a : OwnedAccount)
    (err copied : AdapterRw.solana_program_error.ProgramError)
    (bytes : a.bytes = .Err err) (clone : ops.op35 err = ok copied) :
    OwnedAccount.data ops a = ok (.Err copied) := by
  simp only [OwnedAccount.data, bytes, clone, bind_tc_ok]
 theorem data_error_identity (ops : AdapterRw.Ops) (a : OwnedAccount)
    (err : AdapterRw.solana_program_error.ProgramError)
    (bytes : a.bytes = .Err err) (clone : ops.op35 err = ok err) :
    OwnedAccount.data ops a = ok (.Err err) := data_error ops a err err bytes clone
#print axioms key_exact
#print axioms owner_exact
#print axioms data_ok
#print axioms data_error
#print axioms data_error_identity
end NCK_Getters
end
