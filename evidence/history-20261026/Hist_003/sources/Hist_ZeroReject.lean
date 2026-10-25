import Hist_ZeroHead
set_option autoImplicit false
namespace AspisR1.Hist_ZeroReject
open Aeneas Aeneas.Std Result ControlFlow

theorem reject (bytes : Slice U8) (head : U8)
    (nonempty : 0 < bytes.val.length)
    (read : Slice.index_usize bytes 0#usize = ok head)
    (nonzero : head ≠ 0#u8) :
    AdapterRw.r1_pool_adapter.owned.require_zero bytes =
      ok (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_zero
    AdapterRw.r1_pool_adapter.owned.require_zero_loop
  rw [loop]
  rw [Hist_ZeroHead.body_rejects bytes head nonempty read nonzero]
  rfl

#print axioms reject
end AspisR1.Hist_ZeroReject
