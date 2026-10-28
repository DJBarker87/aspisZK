import NDO_JHi_DigestAssociation
set_option autoImplicit false
namespace AspisR1.JHi_AfterstateLoopAssociation
open Aeneas Aeneas.Std Result

theorem source (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 8#usize))) (out : Array U8 688#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body
  simp only [JHi_DigestAssociation.encode]
  rfl
#print axioms source
end AspisR1.JHi_AfterstateLoopAssociation
