import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NMS_Emitted
open Aeneas Aeneas.Std Result AdapterRw
abbrev AuthCall := solana_pubkey.Pubkey → Slice r1_pool_adapter.owned.OwnedAccount →
 solana_pubkey.Pubkey → U8 → U64 → Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts solana_program_error.ProgramError)
def get (ops : Ops)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error1 =>
    let pe ←
      ops.op35 error1
    ok (core.result.Result.Err pe)
end NMS_Emitted
