import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.Hist_ZeroHead
open Aeneas Aeneas.Std Result ControlFlow

/-- Reject immediately at the first nonzero byte. No large zero scan or
unfolding of a concrete 1768-byte account is needed. -/
theorem body_rejects (bytes : Slice U8) (head : U8)
    (nonempty : 0 < bytes.val.length)
    (read : Slice.index_usize bytes 0#usize = ok head)
    (nonzero : head ≠ 0#u8) :
    AdapterRw.r1_pool_adapter.owned.require_zero_loop.body bytes 0#usize =
      ok (done (some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized))) := by
  simp only [AdapterRw.r1_pool_adapter.owned.require_zero_loop.body]
  have within : (0#usize) < Slice.len bytes := by scalar_tac
  simp only [within, ↓reduceIte, read, bind_tc_ok, bne_iff_ne]
  exact if_pos nonzero

#print axioms body_rejects
end AspisR1.Hist_ZeroHead
