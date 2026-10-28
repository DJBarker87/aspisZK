import NDO_JHi_AfterstateConstants
set_option autoImplicit false
namespace AspisR1.JHi_AfterstateDecoderAction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct JHi_AfterstateBody

theorem source (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (validated : AspisR1TerminalDecoder.pool_v1.pair_terminal.validate_verified_afterstate value=ok (.Ok ())) :
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 value=
    (body value >>= fun out=>ok (core.result.Result.Ok out)) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
    JHi_DigestAssociation.encode,JHi_AfterstateLoopAssociation.source,JHi_AfterstateConstants.c0,JHi_AfterstateConstants.c1,JHi_AfterstateConstants.c2,JHi_AfterstateConstants.c3]
  congr 1
#print axioms source
end AspisR1.JHi_AfterstateDecoderAction
